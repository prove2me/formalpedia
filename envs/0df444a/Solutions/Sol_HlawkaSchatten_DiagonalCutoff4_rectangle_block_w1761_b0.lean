-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1761_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:25:29.514053+00:00
-- url     : https://prove2.me/submissions/9ae73150-00e6-4ea7-aa94-c6200e35f428

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1761_s0_0 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-563189309/5000000000 : ℝ)*x 0 + (2799030381/5000000000 : ℝ)*x 1 + (1248370637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563189309/5000000000 : ℝ)^5951 ≤ (1430941259471/20000000000000 : ℝ)^4927 := by
    have hnat : (563189309 : ℕ)^5951*20000000000000^4927 ≤ 1430941259471^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563189309 5000000000 1430941259471 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2799030381/5000000000 : ℝ)^5951 ≤ (49621645298783/100000000000000 : ℝ)^4927 := by
    have hnat : (2799030381 : ℕ)^5951*100000000000000^4927 ≤ 49621645298783^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799030381 5000000000 49621645298783 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248370637/2500000000 : ℝ)^5951 ≤ (1350739012333/3125000000000 : ℝ)^4927 := by
    have hnat : (1248370637 : ℕ)^5951*3125000000000^4927 ≤ 1350739012333^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248370637 2500000000 1350739012333 3125000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563189309/5000000000 : ℝ), (2799030381/5000000000 : ℝ), (1248370637/2500000000 : ℝ)] ![(1430941259471/20000000000000 : ℝ), (49621645298783/100000000000000 : ℝ), (1350739012333/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563189309/5000000000 : ℝ)|^5951 ≤ (1430941259471/20000000000000 : ℝ)^4927
        have hw : |(-563189309/5000000000 : ℝ)|=(563189309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2799030381/5000000000 : ℝ)|^5951 ≤ (49621645298783/100000000000000 : ℝ)^4927
        have hw : |(2799030381/5000000000 : ℝ)|=(2799030381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248370637/2500000000 : ℝ)|^5951 ≤ (1350739012333/3125000000000 : ℝ)^4927
        have hw : |(1248370637/2500000000 : ℝ)|=(1248370637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_1 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339832261/2500000000 : ℝ)*x 0 + (-28981407/200000000 : ℝ)*x 1 + (4993483673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339832261/2500000000 : ℝ)^5951 ≤ (4707715983717/10000000000000 : ℝ)^4927 := by
    have hnat : (1339832261 : ℕ)^5951*10000000000000^4927 ≤ 4707715983717^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339832261 2500000000 4707715983717 10000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28981407/200000000 : ℝ)^5951 ≤ (2424794997939/25000000000000 : ℝ)^4927 := by
    have hnat : (28981407 : ℕ)^5951*25000000000000^4927 ≤ 2424794997939^4927*200000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28981407 200000000 2424794997939 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4993483673/10000000000 : ℝ)^5951 ≤ (10805915039141/25000000000000 : ℝ)^4927 := by
    have hnat : (4993483673 : ℕ)^5951*25000000000000^4927 ≤ 10805915039141^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993483673 10000000000 10805915039141 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339832261/2500000000 : ℝ), (-28981407/200000000 : ℝ), (4993483673/10000000000 : ℝ)] ![(4707715983717/10000000000000 : ℝ), (2424794997939/25000000000000 : ℝ), (10805915039141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339832261/2500000000 : ℝ)|^5951 ≤ (4707715983717/10000000000000 : ℝ)^4927
        have hw : |(1339832261/2500000000 : ℝ)|=(1339832261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28981407/200000000 : ℝ)|^5951 ≤ (2424794997939/25000000000000 : ℝ)^4927
        have hw : |(-28981407/200000000 : ℝ)|=(28981407/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4993483673/10000000000 : ℝ)|^5951 ≤ (10805915039141/25000000000000 : ℝ)^4927
        have hw : |(4993483673/10000000000 : ℝ)|=(4993483673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_2 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359332611/10000000000 : ℝ)*x 0 + (4993481203/10000000000 : ℝ)*x 1 + (-1449068863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359332611/10000000000 : ℝ)^5951 ≤ (47077197682331/100000000000000 : ℝ)^4927 := by
    have hnat : (5359332611 : ℕ)^5951*100000000000000^4927 ≤ 47077197682331^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359332611 10000000000 47077197682331 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993481203/10000000000 : ℝ)^5951 ≤ (43223634332641/100000000000000 : ℝ)^4927 := by
    have hnat : (4993481203 : ℕ)^5951*100000000000000^4927 ≤ 43223634332641^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993481203 10000000000 43223634332641 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449068863/10000000000 : ℝ)^5951 ≤ (151549499533/1562500000000 : ℝ)^4927 := by
    have hnat : (1449068863 : ℕ)^5951*1562500000000^4927 ≤ 151549499533^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449068863 10000000000 151549499533 1562500000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359332611/10000000000 : ℝ), (4993481203/10000000000 : ℝ), (-1449068863/10000000000 : ℝ)] ![(47077197682331/100000000000000 : ℝ), (43223634332641/100000000000000 : ℝ), (151549499533/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359332611/10000000000 : ℝ)|^5951 ≤ (47077197682331/100000000000000 : ℝ)^4927
        have hw : |(5359332611/10000000000 : ℝ)|=(5359332611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993481203/10000000000 : ℝ)|^5951 ≤ (43223634332641/100000000000000 : ℝ)^4927
        have hw : |(4993481203/10000000000 : ℝ)|=(4993481203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1449068863/10000000000 : ℝ)|^5951 ≤ (151549499533/1562500000000 : ℝ)^4927
        have hw : |(-1449068863/10000000000 : ℝ)|=(1449068863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_3 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (123798829/312500000 : ℝ)*x 0 + (598745931/2000000000 : ℝ)*x 1 + (2534750947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123798829/312500000 : ℝ)^5951 ≤ (32680549537249/100000000000000 : ℝ)^4927 := by
    have hnat : (123798829 : ℕ)^5951*100000000000000^4927 ≤ 32680549537249^4927*312500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123798829 312500000 32680549537249 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598745931/2000000000 : ℝ)^5951 ≤ (11649882599863/50000000000000 : ℝ)^4927 := by
    have hnat : (598745931 : ℕ)^5951*50000000000000^4927 ≤ 11649882599863^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598745931 2000000000 11649882599863 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534750947/5000000000 : ℝ)^5951 ≤ (44019685252669/100000000000000 : ℝ)^4927 := by
    have hnat : (2534750947 : ℕ)^5951*100000000000000^4927 ≤ 44019685252669^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534750947 5000000000 44019685252669 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123798829/312500000 : ℝ), (598745931/2000000000 : ℝ), (2534750947/5000000000 : ℝ)] ![(32680549537249/100000000000000 : ℝ), (11649882599863/50000000000000 : ℝ), (44019685252669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123798829/312500000 : ℝ)|^5951 ≤ (32680549537249/100000000000000 : ℝ)^4927
        have hw : |(123798829/312500000 : ℝ)|=(123798829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598745931/2000000000 : ℝ)|^5951 ≤ (11649882599863/50000000000000 : ℝ)^4927
        have hw : |(598745931/2000000000 : ℝ)|=(598745931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534750947/5000000000 : ℝ)|^5951 ≤ (44019685252669/100000000000000 : ℝ)^4927
        have hw : |(2534750947/5000000000 : ℝ)|=(2534750947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_4 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1127532023/10000000000 : ℝ)*x 0 + (5008619057/10000000000 : ℝ)*x 1 + (2791221877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127532023/10000000000 : ℝ)^5951 ≤ (3581778144179/50000000000000 : ℝ)^4927 := by
    have hnat : (1127532023 : ℕ)^5951*50000000000000^4927 ≤ 3581778144179^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127532023 10000000000 3581778144179 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008619057/10000000000 : ℝ)^5951 ≤ (21690975428171/50000000000000 : ℝ)^4927 := by
    have hnat : (5008619057 : ℕ)^5951*50000000000000^4927 ≤ 21690975428171^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008619057 10000000000 21690975428171 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791221877/5000000000 : ℝ)^5951 ≤ (49454492843681/100000000000000 : ℝ)^4927 := by
    have hnat : (2791221877 : ℕ)^5951*100000000000000^4927 ≤ 49454492843681^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791221877 5000000000 49454492843681 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1127532023/10000000000 : ℝ), (5008619057/10000000000 : ℝ), (2791221877/5000000000 : ℝ)] ![(3581778144179/50000000000000 : ℝ), (21690975428171/50000000000000 : ℝ), (49454492843681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1127532023/10000000000 : ℝ)|^5951 ≤ (3581778144179/50000000000000 : ℝ)^4927
        have hw : |(-1127532023/10000000000 : ℝ)|=(1127532023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008619057/10000000000 : ℝ)|^5951 ≤ (21690975428171/50000000000000 : ℝ)^4927
        have hw : |(5008619057/10000000000 : ℝ)|=(5008619057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2791221877/5000000000 : ℝ)|^5951 ≤ (49454492843681/100000000000000 : ℝ)^4927
        have hw : |(2791221877/5000000000 : ℝ)|=(2791221877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_5 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299715051/2500000000 : ℝ)*x 0 + (-860108211/10000000000 : ℝ)*x 1 + (1395610927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299715051/2500000000 : ℝ)^5951 ≤ (5672494667411/12500000000000 : ℝ)^4927 := by
    have hnat : (1299715051 : ℕ)^5951*12500000000000^4927 ≤ 5672494667411^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299715051 2500000000 5672494667411 12500000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860108211/10000000000 : ℝ)^5951 ≤ (645693786723/12500000000000 : ℝ)^4927 := by
    have hnat : (860108211 : ℕ)^5951*12500000000000^4927 ≤ 645693786723^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860108211 10000000000 645693786723 12500000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395610927/2500000000 : ℝ)^5951 ≤ (1978179694059/4000000000000 : ℝ)^4927 := by
    have hnat : (1395610927 : ℕ)^5951*4000000000000^4927 ≤ 1978179694059^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395610927 2500000000 1978179694059 4000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299715051/2500000000 : ℝ), (-860108211/10000000000 : ℝ), (1395610927/2500000000 : ℝ)] ![(5672494667411/12500000000000 : ℝ), (645693786723/12500000000000 : ℝ), (1978179694059/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299715051/2500000000 : ℝ)|^5951 ≤ (5672494667411/12500000000000 : ℝ)^4927
        have hw : |(1299715051/2500000000 : ℝ)|=(1299715051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-860108211/10000000000 : ℝ)|^5951 ≤ (645693786723/12500000000000 : ℝ)^4927
        have hw : |(-860108211/10000000000 : ℝ)|=(860108211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395610927/2500000000 : ℝ)|^5951 ≤ (1978179694059/4000000000000 : ℝ)^4927
        have hw : |(1395610927/2500000000 : ℝ)|=(1395610927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_6 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299714963/2500000000 : ℝ)*x 0 + (1116488789/2000000000 : ℝ)*x 1 + (-860108373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299714963/2500000000 : ℝ)^5951 ≤ (8863272193/19531250000 : ℝ)^4927 := by
    have hnat : (1299714963 : ℕ)^5951*19531250000^4927 ≤ 8863272193^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299714963 2500000000 8863272193 19531250000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116488789/2000000000 : ℝ)^5951 ≤ (9890898977481/20000000000000 : ℝ)^4927 := by
    have hnat : (1116488789 : ℕ)^5951*20000000000000^4927 ≤ 9890898977481^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116488789 2000000000 9890898977481 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860108373/10000000000 : ℝ)^5951 ≤ (2582775734457/50000000000000 : ℝ)^4927 := by
    have hnat : (860108373 : ℕ)^5951*50000000000000^4927 ≤ 2582775734457^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860108373 10000000000 2582775734457 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299714963/2500000000 : ℝ), (1116488789/2000000000 : ℝ), (-860108373/10000000000 : ℝ)] ![(8863272193/19531250000 : ℝ), (9890898977481/20000000000000 : ℝ), (2582775734457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299714963/2500000000 : ℝ)|^5951 ≤ (8863272193/19531250000 : ℝ)^4927
        have hw : |(1299714963/2500000000 : ℝ)|=(1299714963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1116488789/2000000000 : ℝ)|^5951 ≤ (9890898977481/20000000000000 : ℝ)^4927
        have hw : |(1116488789/2000000000 : ℝ)|=(1116488789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-860108373/10000000000 : ℝ)|^5951 ≤ (2582775734457/50000000000000 : ℝ)^4927
        have hw : |(-860108373/10000000000 : ℝ)|=(860108373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s0_7 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (991381667/2500000000 : ℝ)*x 0 + (1003505907/2000000000 : ℝ)*x 1 + (190459443/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991381667/2500000000 : ℝ)^5951 ≤ (32720052016473/100000000000000 : ℝ)^4927 := by
    have hnat : (991381667 : ℕ)^5951*100000000000000^4927 ≤ 32720052016473^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991381667 2500000000 32720052016473 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003505907/2000000000 : ℝ)^5951 ≤ (43475186014173/100000000000000 : ℝ)^4927 := by
    have hnat : (1003505907 : ℕ)^5951*100000000000000^4927 ≤ 43475186014173^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003505907 2000000000 43475186014173 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190459443/625000000 : ℝ)^5951 ≤ (23804761944437/100000000000000 : ℝ)^4927 := by
    have hnat : (190459443 : ℕ)^5951*100000000000000^4927 ≤ 23804761944437^4927*625000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190459443 625000000 23804761944437 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(991381667/2500000000 : ℝ), (1003505907/2000000000 : ℝ), (190459443/625000000 : ℝ)] ![(32720052016473/100000000000000 : ℝ), (43475186014173/100000000000000 : ℝ), (23804761944437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(991381667/2500000000 : ℝ)|^5951 ≤ (32720052016473/100000000000000 : ℝ)^4927
        have hw : |(991381667/2500000000 : ℝ)|=(991381667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003505907/2000000000 : ℝ)|^5951 ≤ (43475186014173/100000000000000 : ℝ)^4927
        have hw : |(1003505907/2000000000 : ℝ)|=(1003505907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190459443/625000000 : ℝ)|^5951 ≤ (23804761944437/100000000000000 : ℝ)^4927
        have hw : |(190459443/625000000 : ℝ)|=(190459443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1761_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5061/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (5935/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5935 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5935*1^1024 ≤ 0^1024*1^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5935/1024 : ℝ) ≤ (246916509988108879/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5935 ≤ (246916509988108879/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5935*50000000000000000000^1024 ≤ 246916509988108879^1024*5^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 246916509988108879 50000000000000000000 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (246916509988108879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5935 := by
      have hnat : (1 : ℕ)^1024*1^5935 ≤ 1^5935*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50246916509988108879/50000000000000000000 : ℝ) ≤ (2502125757883429/2500000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (50246916509988108879/50000000000000000000 : ℝ)^1024 ≤ (2502125757883429/2500000000000000 : ℝ)^5935 := by
      have hnat : (50246916509988108879 : ℕ)^1024*2500000000000000^5935 ≤ 2502125757883429^5935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50246916509988108879 50000000000000000000 2502125757883429 2500000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502125757883429/2500000000000000 : ℝ)) (X := (50246916509988108879/50000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25246916509988108879/25000000000000000000 : ℝ) ≤ (1252125757883429/1250000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (25246916509988108879/25000000000000000000 : ℝ)^1024 ≤ (1252125757883429/1250000000000000 : ℝ)^5935 := by
      have hnat : (25246916509988108879 : ℕ)^1024*1250000000000000^5935 ≤ 1252125757883429^5935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25246916509988108879 25000000000000000000 1252125757883429 1250000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252125757883429/1250000000000000 : ℝ)) (X := (25246916509988108879/25000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2125757883429/1000000000000000 : ℝ)*(0 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2125757883429/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(246916509988108879/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2125757883429/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5935/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2125757883429/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2502125757883429/2500000000000000 : ℝ) by norm_num, show 1+(246916509988108879/50000000000000000000 : ℝ)+(0 : ℝ)=(50246916509988108879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(246916509988108879/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2125757883429/1000000000000000 : ℝ)*(2/5 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2125757883429/1000000000000000 : ℝ)*(2/5 : ℝ)=(1252125757883429/1250000000000000 : ℝ) by norm_num, show 1+2*(246916509988108879/50000000000000000000 : ℝ)=(25246916509988108879/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2125757883429/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2125757883429/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2125757883429/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2125757883429/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2125757883429/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2125757883429/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-563189309/5000000000 : ℝ)*X 0 0+(2799030381/5000000000 : ℝ)*X 0 1+(1248370637/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339832261/2500000000 : ℝ)*X 1 0+(-28981407/200000000 : ℝ)*X 1 1+(4993483673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359332611/10000000000 : ℝ)*X 2 0+(4993481203/10000000000 : ℝ)*X 2 1+(-1449068863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((123798829/312500000 : ℝ)*X 0 0+(598745931/2000000000 : ℝ)*X 0 1+(2534750947/5000000000 : ℝ)*X 0 2+(123798829/312500000 : ℝ)*X 1 0+(598745931/2000000000 : ℝ)*X 1 1+(2534750947/5000000000 : ℝ)*X 1 2+(123798829/312500000 : ℝ)*X 2 0+(598745931/2000000000 : ℝ)*X 2 1+(2534750947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1127532023/10000000000 : ℝ)*X 0 0+(5008619057/10000000000 : ℝ)*X 0 1+(2791221877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299715051/2500000000 : ℝ)*X 1 0+(-860108211/10000000000 : ℝ)*X 1 1+(1395610927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299714963/2500000000 : ℝ)*X 2 0+(1116488789/2000000000 : ℝ)*X 2 1+(-860108373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((991381667/2500000000 : ℝ)*X 0 0+(1003505907/2000000000 : ℝ)*X 0 1+(190459443/625000000 : ℝ)*X 0 2+(991381667/2500000000 : ℝ)*X 1 0+(1003505907/2000000000 : ℝ)*X 1 1+(190459443/625000000 : ℝ)*X 1 2+(991381667/2500000000 : ℝ)*X 2 0+(1003505907/2000000000 : ℝ)*X 2 1+(190459443/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1899342105607410317151/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37340759/20000000000000 : ℝ)*(base19) + (743280253/100000000000000 : ℝ)*(base23) + (2940387/2000000000000 : ℝ)*(base24) + (13307433/6250000000000 : ℝ)*(upper4) + (68956903/50000000000000 : ℝ)*(upper5) + (53395001467327/5000000000000 : ℝ)*(major0) + (53395001467327/5000000000000 : ℝ)*(major1) + (53395001467327/5000000000000 : ℝ)*(major2) + (827022284520683/50000000000000 : ℝ)*(sp0) + (1654049128899907/100000000000000 : ℝ)*(sp1) + (827024212652049/50000000000000 : ℝ)*(sp2) + (240874692061031/50000000000000 : ℝ)*(sp3) + (949312467/20000000000000 : ℝ)*(sp4) + (1333642747/100000000000000 : ℝ)*(sp7) + (481750717764809/100000000000000 : ℝ)*(f.failure) + (827024657801851/50000000000000 : ℝ)*(f.sum) + (7111558626783/2500000000000000000000000000 : ℝ)*base65 + (10197417014283/5000000000000000000000000000 : ℝ)*base67 + (27825666614283/5000000000000000000000000000 : ℝ)*base69 + (27569975024283/5000000000000000000000000000 : ℝ)*base71 + (6628991288217/2500000000000000000000000000 : ℝ)*base74 + (1435494650717/5000000000000000000000000000 : ℝ)*base76 + (34323270174283/5000000000000000000000000000 : ℝ)*base77 + (31982562479283/5000000000000000000000000000 : ℝ)*base79 + (9586790750717/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (39842397/10000000000000000000000 : ℝ)*base90 + (39842397/10000000000000000000000 : ℝ)*base92 + (39842397/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206862526924356664767/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396995891/25000000000000 : ℝ)*(base19) + (45823203/3125000000000 : ℝ)*(base23) + (20234061/100000000000000 : ℝ)*(base32) + (54827967/20000000000000 : ℝ)*(upper3) + (53041199/25000000000000 : ℝ)*(upper5) + (562565026497/50000000000 : ℝ)*(major0) + (562565026497/50000000000 : ℝ)*(major1) + (562565026497/50000000000 : ℝ)*(major2) + (7120083497/100000000000000 : ℝ)*(sp1) + (875213601/12500000000000 : ℝ)*(sp2) + (87134576127291/5000000000000 : ℝ)*(sp4) + (43567070361969/2500000000000 : ℝ)*(sp5) + (435670763623629/25000000000000 : ℝ)*(sp6) + (507568287391413/100000000000000 : ℝ)*(sp7) + (253784153812737/50000000000000 : ℝ)*(f.failure) + (87134576127291/5000000000000 : ℝ)*(f.sum) + (4750482387/25000000000000000000000000 : ℝ)*base66 + (160006516537/50000000000000000000000000 : ℝ)*base68 + (35761437013/50000000000000000000000000 : ℝ)*base69 + (455485571387/50000000000000000000000000 : ℝ)*base72 + (3237869011/3125000000000000000000000 : ℝ)*base73 + (198742477037/50000000000000000000000000 : ℝ)*base76 + (119608341987/50000000000000000000000000 : ℝ)*base78 + (74994011737/50000000000000000000000000 : ℝ)*base80 + (36167271087/25000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3885579/5000000000000000000000 : ℝ)*base89 + (3885579/5000000000000000000000 : ℝ)*base91 + (3885579/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1761_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5061/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1761_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1761_s1_0 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-232573163/2000000000 : ℝ)*x 0 + (171394987/312500000 : ℝ)*x 1 + (2541178081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232573163/2000000000 : ℝ)^5951 ≤ (743557444887/10000000000000 : ℝ)^4927 := by
    have hnat : (232573163 : ℕ)^5951*10000000000000^4927 ≤ 743557444887^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232573163 2000000000 743557444887 10000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171394987/312500000 : ℝ)^5951 ≤ (48409890358239/100000000000000 : ℝ)^4927 := by
    have hnat : (171394987 : ℕ)^5951*100000000000000^4927 ≤ 48409890358239^4927*312500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171394987 312500000 48409890358239 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541178081/5000000000 : ℝ)^5951 ≤ (8830907036431/20000000000000 : ℝ)^4927 := by
    have hnat : (2541178081 : ℕ)^5951*20000000000000^4927 ≤ 8830907036431^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541178081 5000000000 8830907036431 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232573163/2000000000 : ℝ), (171394987/312500000 : ℝ), (2541178081/5000000000 : ℝ)] ![(743557444887/10000000000000 : ℝ), (48409890358239/100000000000000 : ℝ), (8830907036431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232573163/2000000000 : ℝ)|^5951 ≤ (743557444887/10000000000000 : ℝ)^4927
        have hw : |(-232573163/2000000000 : ℝ)|=(232573163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171394987/312500000 : ℝ)|^5951 ≤ (48409890358239/100000000000000 : ℝ)^4927
        have hw : |(171394987/312500000 : ℝ)|=(171394987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541178081/5000000000 : ℝ)|^5951 ≤ (8830907036431/20000000000000 : ℝ)^4927
        have hw : |(2541178081/5000000000 : ℝ)|=(2541178081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_1 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53292201/100000000 : ℝ)*x 0 + (-1372997209/10000000000 : ℝ)*x 1 + (5082355997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53292201/100000000 : ℝ)^5951 ≤ (46757896722277/100000000000000 : ℝ)^4927 := by
    have hnat : (53292201 : ℕ)^5951*100000000000000^4927 ≤ 46757896722277^4927*100000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53292201 100000000 46757896722277 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372997209/10000000000 : ℝ)^5951 ≤ (9087569807527/100000000000000 : ℝ)^4927 := by
    have hnat : (1372997209 : ℕ)^5951*100000000000000^4927 ≤ 9087569807527^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372997209 10000000000 9087569807527 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082355997/10000000000 : ℝ)^5951 ≤ (44154533450739/100000000000000 : ℝ)^4927 := by
    have hnat : (5082355997 : ℕ)^5951*100000000000000^4927 ≤ 44154533450739^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082355997 10000000000 44154533450739 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53292201/100000000 : ℝ), (-1372997209/10000000000 : ℝ), (5082355997/10000000000 : ℝ)] ![(46757896722277/100000000000000 : ℝ), (9087569807527/100000000000000 : ℝ), (44154533450739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53292201/100000000 : ℝ)|^5951 ≤ (46757896722277/100000000000000 : ℝ)^4927
        have hw : |(53292201/100000000 : ℝ)|=(53292201/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1372997209/10000000000 : ℝ)|^5951 ≤ (9087569807527/100000000000000 : ℝ)^4927
        have hw : |(-1372997209/10000000000 : ℝ)|=(1372997209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082355997/10000000000 : ℝ)|^5951 ≤ (44154533450739/100000000000000 : ℝ)^4927
        have hw : |(5082355997/10000000000 : ℝ)|=(5082355997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_2 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5329218331/10000000000 : ℝ)*x 0 + (5082357893/10000000000 : ℝ)*x 1 + (-686498533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5329218331/10000000000 : ℝ)^5951 ≤ (2922367373469/6250000000000 : ℝ)^4927 := by
    have hnat : (5329218331 : ℕ)^5951*6250000000000^4927 ≤ 2922367373469^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329218331 10000000000 2922367373469 6250000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082357893/10000000000 : ℝ)^5951 ≤ (44154553346289/100000000000000 : ℝ)^4927 := by
    have hnat : (5082357893 : ℕ)^5951*100000000000000^4927 ≤ 44154553346289^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082357893 10000000000 44154553346289 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686498533/5000000000 : ℝ)^5951 ≤ (9087568664329/100000000000000 : ℝ)^4927 := by
    have hnat : (686498533 : ℕ)^5951*100000000000000^4927 ≤ 9087568664329^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686498533 5000000000 9087568664329 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5329218331/10000000000 : ℝ), (5082357893/10000000000 : ℝ), (-686498533/5000000000 : ℝ)] ![(2922367373469/6250000000000 : ℝ), (44154553346289/100000000000000 : ℝ), (9087568664329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5329218331/10000000000 : ℝ)|^5951 ≤ (2922367373469/6250000000000 : ℝ)^4927
        have hw : |(5329218331/10000000000 : ℝ)|=(5329218331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082357893/10000000000 : ℝ)|^5951 ≤ (44154553346289/100000000000000 : ℝ)^4927
        have hw : |(5082357893/10000000000 : ℝ)|=(5082357893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-686498533/5000000000 : ℝ)|^5951 ≤ (9087568664329/100000000000000 : ℝ)^4927
        have hw : |(-686498533/5000000000 : ℝ)|=(686498533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_3 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3998150723/10000000000 : ℝ)*x 0 + (104325467/312500000 : ℝ)*x 1 + (2359809071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3998150723/10000000000 : ℝ)^5951 ≤ (2065341276231/6250000000000 : ℝ)^4927 := by
    have hnat : (3998150723 : ℕ)^5951*6250000000000^4927 ≤ 2065341276231^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998150723 10000000000 2065341276231 6250000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104325467/312500000 : ℝ)^5951 ≤ (5315518174827/20000000000000 : ℝ)^4927 := by
    have hnat : (104325467 : ℕ)^5951*20000000000000^4927 ≤ 5315518174827^4927*312500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104325467 312500000 5315518174827 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2359809071/5000000000 : ℝ)^5951 ≤ (40376948697721/100000000000000 : ℝ)^4927 := by
    have hnat : (2359809071 : ℕ)^5951*100000000000000^4927 ≤ 40376948697721^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359809071 5000000000 40376948697721 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3998150723/10000000000 : ℝ), (104325467/312500000 : ℝ), (2359809071/5000000000 : ℝ)] ![(2065341276231/6250000000000 : ℝ), (5315518174827/20000000000000 : ℝ), (40376948697721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3998150723/10000000000 : ℝ)|^5951 ≤ (2065341276231/6250000000000 : ℝ)^4927
        have hw : |(3998150723/10000000000 : ℝ)|=(3998150723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104325467/312500000 : ℝ)|^5951 ≤ (5315518174827/20000000000000 : ℝ)^4927
        have hw : |(104325467/312500000 : ℝ)|=(104325467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2359809071/5000000000 : ℝ)|^5951 ≤ (40376948697721/100000000000000 : ℝ)^4927
        have hw : |(2359809071/5000000000 : ℝ)|=(2359809071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_4 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1163203939/10000000000 : ℝ)*x 0 + (636134621/1250000000 : ℝ)*x 1 + (5477777587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163203939/10000000000 : ℝ)^5951 ≤ (1859546474289/25000000000000 : ℝ)^4927 := by
    have hnat : (1163203939 : ℕ)^5951*25000000000000^4927 ≤ 1859546474289^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163203939 10000000000 1859546474289 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636134621/1250000000 : ℝ)^5951 ≤ (44225069199993/100000000000000 : ℝ)^4927 := by
    have hnat : (636134621 : ℕ)^5951*100000000000000^4927 ≤ 44225069199993^4927*1250000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636134621 1250000000 44225069199993 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477777587/10000000000 : ℝ)^5951 ≤ (48336744888977/100000000000000 : ℝ)^4927 := by
    have hnat : (5477777587 : ℕ)^5951*100000000000000^4927 ≤ 48336744888977^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477777587 10000000000 48336744888977 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1163203939/10000000000 : ℝ), (636134621/1250000000 : ℝ), (5477777587/10000000000 : ℝ)] ![(1859546474289/25000000000000 : ℝ), (44225069199993/100000000000000 : ℝ), (48336744888977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1163203939/10000000000 : ℝ)|^5951 ≤ (1859546474289/25000000000000 : ℝ)^4927
        have hw : |(-1163203939/10000000000 : ℝ)|=(1163203939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636134621/1250000000 : ℝ)|^5951 ≤ (44225069199993/100000000000000 : ℝ)^4927
        have hw : |(636134621/1250000000 : ℝ)|=(636134621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477777587/10000000000 : ℝ)|^5951 ≤ (48336744888977/100000000000000 : ℝ)^4927
        have hw : |(5477777587/10000000000 : ℝ)|=(5477777587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_5 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222937953/10000000000 : ℝ)*x 0 + (-977575327/10000000000 : ℝ)*x 1 + (2738888749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222937953/10000000000 : ℝ)^5951 ≤ (45633930559329/100000000000000 : ℝ)^4927 := by
    have hnat : (5222937953 : ℕ)^5951*100000000000000^4927 ≤ 45633930559329^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222937953 10000000000 45633930559329 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977575327/10000000000 : ℝ)^5951 ≤ (1507331371751/25000000000000 : ℝ)^4927 := by
    have hnat : (977575327 : ℕ)^5951*25000000000000^4927 ≤ 1507331371751^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977575327 10000000000 1507331371751 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738888749/5000000000 : ℝ)^5951 ≤ (12084185985101/25000000000000 : ℝ)^4927 := by
    have hnat : (2738888749 : ℕ)^5951*25000000000000^4927 ≤ 12084185985101^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738888749 5000000000 12084185985101 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222937953/10000000000 : ℝ), (-977575327/10000000000 : ℝ), (2738888749/5000000000 : ℝ)] ![(45633930559329/100000000000000 : ℝ), (1507331371751/25000000000000 : ℝ), (12084185985101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222937953/10000000000 : ℝ)|^5951 ≤ (45633930559329/100000000000000 : ℝ)^4927
        have hw : |(5222937953/10000000000 : ℝ)|=(5222937953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977575327/10000000000 : ℝ)|^5951 ≤ (1507331371751/25000000000000 : ℝ)^4927
        have hw : |(-977575327/10000000000 : ℝ)|=(977575327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738888749/5000000000 : ℝ)|^5951 ≤ (12084185985101/25000000000000 : ℝ)^4927
        have hw : |(2738888749/5000000000 : ℝ)|=(2738888749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_6 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222938253/10000000000 : ℝ)*x 0 + (5477776873/10000000000 : ℝ)*x 1 + (-244393949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222938253/10000000000 : ℝ)^5951 ≤ (45633933725261/100000000000000 : ℝ)^4927 := by
    have hnat : (5222938253 : ℕ)^5951*100000000000000^4927 ≤ 45633933725261^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222938253 10000000000 45633933725261 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477776873/10000000000 : ℝ)^5951 ≤ (48336737279083/100000000000000 : ℝ)^4927 := by
    have hnat : (5477776873 : ℕ)^5951*100000000000000^4927 ≤ 48336737279083^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477776873 10000000000 48336737279083 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244393949/2500000000 : ℝ)^5951 ≤ (602932898081/10000000000000 : ℝ)^4927 := by
    have hnat : (244393949 : ℕ)^5951*10000000000000^4927 ≤ 602932898081^4927*2500000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244393949 2500000000 602932898081 10000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222938253/10000000000 : ℝ), (5477776873/10000000000 : ℝ), (-244393949/2500000000 : ℝ)] ![(45633933725261/100000000000000 : ℝ), (48336737279083/100000000000000 : ℝ), (602932898081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222938253/10000000000 : ℝ)|^5951 ≤ (45633933725261/100000000000000 : ℝ)^4927
        have hw : |(5222938253/10000000000 : ℝ)|=(5222938253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477776873/10000000000 : ℝ)|^5951 ≤ (48336737279083/100000000000000 : ℝ)^4927
        have hw : |(5477776873/10000000000 : ℝ)|=(5477776873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244393949/2500000000 : ℝ)|^5951 ≤ (602932898081/10000000000000 : ℝ)^4927
        have hw : |(-244393949/2500000000 : ℝ)|=(244393949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s1_7 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1999657009/5000000000 : ℝ)*x 0 + (4696544249/10000000000 : ℝ)*x 1 + (336197279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999657009/5000000000 : ℝ)^5951 ≤ (1322282956681/4000000000000 : ℝ)^4927 := by
    have hnat : (1999657009 : ℕ)^5951*4000000000000^4927 ≤ 1322282956681^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999657009 5000000000 1322282956681 4000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4696544249/10000000000 : ℝ)^5951 ≤ (40138643280973/100000000000000 : ℝ)^4927 := by
    have hnat : (4696544249 : ℕ)^5951*100000000000000^4927 ≤ 40138643280973^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696544249 10000000000 40138643280973 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336197279/1000000000 : ℝ)^5951 ≤ (1072171311403/4000000000000 : ℝ)^4927 := by
    have hnat : (336197279 : ℕ)^5951*4000000000000^4927 ≤ 1072171311403^4927*1000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336197279 1000000000 1072171311403 4000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999657009/5000000000 : ℝ), (4696544249/10000000000 : ℝ), (336197279/1000000000 : ℝ)] ![(1322282956681/4000000000000 : ℝ), (40138643280973/100000000000000 : ℝ), (1072171311403/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999657009/5000000000 : ℝ)|^5951 ≤ (1322282956681/4000000000000 : ℝ)^4927
        have hw : |(1999657009/5000000000 : ℝ)|=(1999657009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4696544249/10000000000 : ℝ)|^5951 ≤ (40138643280973/100000000000000 : ℝ)^4927
        have hw : |(4696544249/10000000000 : ℝ)|=(4696544249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336197279/1000000000 : ℝ)|^5951 ≤ (1072171311403/4000000000000 : ℝ)^4927
        have hw : |(336197279/1000000000 : ℝ)|=(336197279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1761_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (913/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17807/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (3569/50000 : ℝ) ^ (5935/1024 : ℝ) ≤ (22669716052909/100000000000000000000 : ℝ) := by
    have hpowers : (3569/50000 : ℝ)^5935 ≤ (22669716052909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3569 : ℕ)^5935*100000000000000000000^1024 ≤ 22669716052909^1024*50000^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3569 50000 22669716052909 100000000000000000000 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3569/50000 : ℝ)) (X := (22669716052909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5061/25000 : ℝ) ^ (5935/1024 : ℝ) ≤ (1907190043031271/20000000000000000000 : ℝ) := by
    have hpowers : (5061/25000 : ℝ)^5935 ≤ (1907190043031271/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5061 : ℕ)^5935*20000000000000000000^1024 ≤ 1907190043031271^1024*25000^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5061 25000 1907190043031271 20000000000000000000 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5061/25000 : ℝ)) (X := (1907190043031271/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000022669716052909/50000000000000000000 : ℝ) ≤ (10000000782267393/10000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (50000022669716052909/50000000000000000000 : ℝ)^1024 ≤ (10000000782267393/10000000000000000 : ℝ)^5935 := by
      have hnat : (50000022669716052909 : ℕ)^1024*10000000000000000^5935 ≤ 10000000782267393^5935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000022669716052909 50000000000000000000 10000000782267393 10000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000782267393/10000000000000000 : ℝ)) (X := (50000022669716052909/50000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250597413745700579/6250000000000000000 : ℝ) ≤ (10000164913896281/10000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (6250597413745700579/6250000000000000000 : ℝ)^1024 ≤ (10000164913896281/10000000000000000 : ℝ)^5935 := by
      have hnat : (6250597413745700579 : ℕ)^1024*10000000000000000^5935 ≤ 10000164913896281^5935*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250597413745700579 6250000000000000000 10000164913896281 10000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000164913896281/10000000000000000 : ℝ)) (X := (6250597413745700579/6250000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001907190043031271/10000000000000000000 : ℝ) ≤ (10000329045525169/10000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (10001907190043031271/10000000000000000000 : ℝ)^1024 ≤ (10000329045525169/10000000000000000 : ℝ)^5935 := by
      have hnat : (10001907190043031271 : ℕ)^1024*10000000000000000^5935 ≤ 10000329045525169^5935*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001907190043031271 10000000000000000000 10000329045525169 10000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000329045525169/10000000000000000 : ℝ)) (X := (10001907190043031271/10000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22669716052909/100000000000000000000 : ℝ) ≤ ((13105766710926244757/13106000000000000000 : ℝ)+2*(20516453611/163825000000000 : ℝ)*(3569/50000 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (13105766710926244757/13106000000000000000 : ℝ)+2*(20516453611/163825000000000 : ℝ)*(3569/50000 : ℝ)=(10000000782267393/10000000000000000 : ℝ) by norm_num, show 1+2*(22669716052909/100000000000000000000 : ℝ)=(50000022669716052909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1907190043031271/20000000000000000000 : ℝ)+(22669716052909/100000000000000000000 : ℝ) ≤ ((13105766710926244757/13106000000000000000 : ℝ)+(20516453611/163825000000000 : ℝ)*((5061/25000 : ℝ)+(3569/50000 : ℝ)))^(5935/1024 : ℝ) := by
    rw [show (13105766710926244757/13106000000000000000 : ℝ)+(20516453611/163825000000000 : ℝ)*((5061/25000 : ℝ)+(3569/50000 : ℝ))=(10000164913896281/10000000000000000 : ℝ) by norm_num, show 1+(1907190043031271/20000000000000000000 : ℝ)+(22669716052909/100000000000000000000 : ℝ)=(6250597413745700579/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1907190043031271/20000000000000000000 : ℝ) ≤ ((13105766710926244757/13106000000000000000 : ℝ)+2*(20516453611/163825000000000 : ℝ)*(5061/25000 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (13105766710926244757/13106000000000000000 : ℝ)+2*(20516453611/163825000000000 : ℝ)*(5061/25000 : ℝ)=(10000329045525169/10000000000000000 : ℝ) by norm_num, show 1+2*(1907190043031271/20000000000000000000 : ℝ)=(10001907190043031271/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13105766710926244757/13106000000000000000 : ℝ)*(X 1 0+X 2 0)+(20516453611/163825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (3569/50000 : ℝ)) (hi := (5061/25000 : ℝ)) (c := (13105766710926244757/13106000000000000000 : ℝ)) (alpha := (20516453611/163825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13105766710926244757/13106000000000000000 : ℝ)*(X 0 1+X 2 1)+(20516453611/163825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (3569/50000 : ℝ)) (hi := (5061/25000 : ℝ)) (c := (13105766710926244757/13106000000000000000 : ℝ)) (alpha := (20516453611/163825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13105766710926244757/13106000000000000000 : ℝ)*(X 0 2+X 1 2)+(20516453611/163825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (3569/50000 : ℝ)) (hi := (5061/25000 : ℝ)) (c := (13105766710926244757/13106000000000000000 : ℝ)) (alpha := (20516453611/163825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-232573163/2000000000 : ℝ)*X 0 0+(171394987/312500000 : ℝ)*X 0 1+(2541178081/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53292201/100000000 : ℝ)*X 1 0+(-1372997209/10000000000 : ℝ)*X 1 1+(5082355997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5329218331/10000000000 : ℝ)*X 2 0+(5082357893/10000000000 : ℝ)*X 2 1+(-686498533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3998150723/10000000000 : ℝ)*X 0 0+(104325467/312500000 : ℝ)*X 0 1+(2359809071/5000000000 : ℝ)*X 0 2+(3998150723/10000000000 : ℝ)*X 1 0+(104325467/312500000 : ℝ)*X 1 1+(2359809071/5000000000 : ℝ)*X 1 2+(3998150723/10000000000 : ℝ)*X 2 0+(104325467/312500000 : ℝ)*X 2 1+(2359809071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1163203939/10000000000 : ℝ)*X 0 0+(636134621/1250000000 : ℝ)*X 0 1+(5477777587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5222937953/10000000000 : ℝ)*X 1 0+(-977575327/10000000000 : ℝ)*X 1 1+(2738888749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5222938253/10000000000 : ℝ)*X 2 0+(5477776873/10000000000 : ℝ)*X 2 1+(-244393949/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1999657009/5000000000 : ℝ)*X 0 0+(4696544249/10000000000 : ℝ)*X 0 1+(336197279/1000000000 : ℝ)*X 0 2+(1999657009/5000000000 : ℝ)*X 1 0+(4696544249/10000000000 : ℝ)*X 1 1+(336197279/1000000000 : ℝ)*X 1 2+(1999657009/5000000000 : ℝ)*X 2 0+(4696544249/10000000000 : ℝ)*X 2 1+(336197279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (904049385172176496140761427/65530000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64059903/4000000000000 : ℝ)*(base19) + (183209917/25000000000000 : ℝ)*(base23) + (5795723/25000000000000 : ℝ)*(lower2) + (144172599/50000000000000 : ℝ)*(upper3) + (48158737/20000000000000 : ℝ)*(upper5) + (320984792355437/20000000000000 : ℝ)*(major0) + (320984792355437/20000000000000 : ℝ)*(major1) + (320984792355437/20000000000000 : ℝ)*(major2) + (2485823094664531/100000000000000 : ℝ)*(sp0) + (1242916540377073/50000000000000 : ℝ)*(sp1) + (2485833949412053/100000000000000 : ℝ)*(sp2) + (724009685658113/100000000000000 : ℝ)*(sp3) + (1158758719/10000000000000 : ℝ)*(sp4) + (386972391/12500000000000 : ℝ)*(sp7) + (724012781437241/100000000000000 : ℝ)*(f.failure) + (1242917341125861/50000000000000 : ℝ)*(f.sum) + (283880039923/51195312500000000000000000 : ℝ)*base65 + (2106560728241906191/262120000000000000000000000000000 : ℝ)*base68 + (381261501919906191/262120000000000000000000000000000 : ℝ)*base70 + (289074654136106191/262120000000000000000000000000000 : ℝ)*base72 + (4984619752781/3276500000000000000000000000 : ℝ)*base74 + (1420492076101106191/262120000000000000000000000000000 : ℝ)*base76 + (681837606275266191/262120000000000000000000000000000 : ℝ)*base78 + (244747595931493809/262120000000000000000000000000000 : ℝ)*base79 + (142629928333/51195312500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (68890253/10000000000000000000000 : ℝ)*base90 + (68890253/10000000000000000000000 : ℝ)*base92 + (68890253/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1158757997981644787837168319/81912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122856087/6250000000000 : ℝ)*(base19) + (2522767479/100000000000000 : ℝ)*(base23) + (5495273/1562500000000 : ℝ)*(upper3) + (50383033/25000000000000 : ℝ)*(lower4) + (5013577/2000000000000 : ℝ)*(upper5) + (207623430073211/12500000000000 : ℝ)*(major0) + (207623430073211/12500000000000 : ℝ)*(major1) + (207623430073211/12500000000000 : ℝ)*(major2) + (13007331659/100000000000000 : ℝ)*(sp1) + (14159455051/100000000000000 : ℝ)*(sp2) + (643167572415751/25000000000000 : ℝ)*(sp4) + (1286327658316977/50000000000000 : ℝ)*(sp5) + (1286326803720237/50000000000000 : ℝ)*(sp6) + (749304119965357/100000000000000 : ℝ)*(sp7) + (749304119965357/100000000000000 : ℝ)*(f.failure) + (643167572415751/25000000000000 : ℝ)*(f.sum) + (64923836929961/16382500000000000000000000000 : ℝ)*base65 + (393707791542540273/163825000000000000000000000000000 : ℝ)*base68 + (321608905307734727/163825000000000000000000000000000 : ℝ)*base69 + (11963222638015273/163825000000000000000000000000000 : ℝ)*base72 + (3115035547897/8191250000000000000000000000 : ℝ)*base74 + (433618553353959727/163825000000000000000000000000000 : ℝ)*base75 + (517094913042659727/163825000000000000000000000000000 : ℝ)*base77 + (246547589743234727/163825000000000000000000000000000 : ℝ)*base79 + (3073818432759/4095625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (96916881/10000000000000000000000 : ℝ)*base90 + (96916881/10000000000000000000000 : ℝ)*base92 + (96916881/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1761_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (913/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17807/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1761_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1761_s2_0 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-232698723/2000000000 : ℝ)*x 0 + (5482618111/10000000000 : ℝ)*x 1 + (31774673/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232698723/2000000000 : ℝ)^5951 ≤ (7440423290311/100000000000000 : ℝ)^4927 := by
    have hnat : (232698723 : ℕ)^5951*100000000000000^4927 ≤ 7440423290311^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232698723 2000000000 7440423290311 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482618111/10000000000 : ℝ)^5951 ≤ (48388340485861/100000000000000 : ℝ)^4927 := by
    have hnat : (5482618111 : ℕ)^5951*100000000000000^4927 ≤ 48388340485861^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482618111 10000000000 48388340485861 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31774673/62500000 : ℝ)^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927 := by
    have hnat : (31774673 : ℕ)^5951*25000000000000^4927 ≤ 11042809053411^4927*62500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31774673 62500000 11042809053411 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232698723/2000000000 : ℝ), (5482618111/10000000000 : ℝ), (31774673/62500000 : ℝ)] ![(7440423290311/100000000000000 : ℝ), (48388340485861/100000000000000 : ℝ), (11042809053411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232698723/2000000000 : ℝ)|^5951 ≤ (7440423290311/100000000000000 : ℝ)^4927
        have hw : |(-232698723/2000000000 : ℝ)|=(232698723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482618111/10000000000 : ℝ)|^5951 ≤ (48388340485861/100000000000000 : ℝ)^4927
        have hw : |(5482618111/10000000000 : ℝ)|=(5482618111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31774673/62500000 : ℝ)|^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927
        have hw : |(31774673/62500000 : ℝ)|=(31774673/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_1 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (666081849/1250000000 : ℝ)*x 0 + (-137165713/1000000000 : ℝ)*x 1 + (31774673/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666081849/1250000000 : ℝ)^5951 ≤ (23375953000997/50000000000000 : ℝ)^4927 := by
    have hnat : (666081849 : ℕ)^5951*50000000000000^4927 ≤ 23375953000997^4927*1250000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666081849 1250000000 23375953000997 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137165713/1000000000 : ℝ)^5951 ≤ (907685777623/10000000000000 : ℝ)^4927 := by
    have hnat : (137165713 : ℕ)^5951*10000000000000^4927 ≤ 907685777623^4927*1000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137165713 1000000000 907685777623 10000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31774673/62500000 : ℝ)^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927 := by
    have hnat : (31774673 : ℕ)^5951*25000000000000^4927 ≤ 11042809053411^4927*62500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31774673 62500000 11042809053411 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666081849/1250000000 : ℝ), (-137165713/1000000000 : ℝ), (31774673/62500000 : ℝ)] ![(23375953000997/50000000000000 : ℝ), (907685777623/10000000000000 : ℝ), (11042809053411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666081849/1250000000 : ℝ)|^5951 ≤ (23375953000997/50000000000000 : ℝ)^4927
        have hw : |(666081849/1250000000 : ℝ)|=(666081849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137165713/1000000000 : ℝ)|^5951 ≤ (907685777623/10000000000000 : ℝ)^4927
        have hw : |(-137165713/1000000000 : ℝ)|=(137165713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31774673/62500000 : ℝ)|^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927
        have hw : |(31774673/62500000 : ℝ)|=(31774673/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_2 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (666081849/1250000000 : ℝ)*x 0 + (31774673/62500000 : ℝ)*x 1 + (-137165713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666081849/1250000000 : ℝ)^5951 ≤ (23375953000997/50000000000000 : ℝ)^4927 := by
    have hnat : (666081849 : ℕ)^5951*50000000000000^4927 ≤ 23375953000997^4927*1250000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666081849 1250000000 23375953000997 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31774673/62500000 : ℝ)^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927 := by
    have hnat : (31774673 : ℕ)^5951*25000000000000^4927 ≤ 11042809053411^4927*62500000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31774673 62500000 11042809053411 25000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137165713/1000000000 : ℝ)^5951 ≤ (907685777623/10000000000000 : ℝ)^4927 := by
    have hnat : (137165713 : ℕ)^5951*10000000000000^4927 ≤ 907685777623^4927*1000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137165713 1000000000 907685777623 10000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666081849/1250000000 : ℝ), (31774673/62500000 : ℝ), (-137165713/1000000000 : ℝ)] ![(23375953000997/50000000000000 : ℝ), (11042809053411/25000000000000 : ℝ), (907685777623/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666081849/1250000000 : ℝ)|^5951 ≤ (23375953000997/50000000000000 : ℝ)^4927
        have hw : |(666081849/1250000000 : ℝ)|=(666081849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31774673/62500000 : ℝ)|^5951 ≤ (11042809053411/25000000000000 : ℝ)^4927
        have hw : |(31774673/62500000 : ℝ)|=(31774673/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137165713/1000000000 : ℝ)|^5951 ≤ (907685777623/10000000000000 : ℝ)^4927
        have hw : |(-137165713/1000000000 : ℝ)|=(137165713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_3 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (499833541/1250000000 : ℝ)*x 0 + (3344579341/10000000000 : ℝ)*x 1 + (4713379717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499833541/1250000000 : ℝ)^5951 ≤ (33050627727573/100000000000000 : ℝ)^4927 := by
    have hnat : (499833541 : ℕ)^5951*100000000000000^4927 ≤ 33050627727573^4927*1250000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499833541 1250000000 33050627727573 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3344579341/10000000000 : ℝ)^5951 ≤ (26636877477529/100000000000000 : ℝ)^4927 := by
    have hnat : (3344579341 : ℕ)^5951*100000000000000^4927 ≤ 26636877477529^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344579341 10000000000 26636877477529 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4713379717/10000000000 : ℝ)^5951 ≤ (8062498956561/20000000000000 : ℝ)^4927 := by
    have hnat : (4713379717 : ℕ)^5951*20000000000000^4927 ≤ 8062498956561^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713379717 10000000000 8062498956561 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(499833541/1250000000 : ℝ), (3344579341/10000000000 : ℝ), (4713379717/10000000000 : ℝ)] ![(33050627727573/100000000000000 : ℝ), (26636877477529/100000000000000 : ℝ), (8062498956561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(499833541/1250000000 : ℝ)|^5951 ≤ (33050627727573/100000000000000 : ℝ)^4927
        have hw : |(499833541/1250000000 : ℝ)|=(499833541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3344579341/10000000000 : ℝ)|^5951 ≤ (26636877477529/100000000000000 : ℝ)^4927
        have hw : |(3344579341/10000000000 : ℝ)|=(3344579341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4713379717/10000000000 : ℝ)|^5951 ≤ (8062498956561/20000000000000 : ℝ)^4927
        have hw : |(4713379717/10000000000 : ℝ)|=(4713379717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_4 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1163822939/10000000000 : ℝ)*x 0 + (1018109577/2000000000 : ℝ)*x 1 + (1095176059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163822939/10000000000 : ℝ)^5951 ≤ (7442967056449/100000000000000 : ℝ)^4927 := by
    have hnat : (1163822939 : ℕ)^5951*100000000000000^4927 ≤ 7442967056449^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163822939 10000000000 7442967056449 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018109577/2000000000 : ℝ)^5951 ≤ (2765031804567/6250000000000 : ℝ)^4927 := by
    have hnat : (1018109577 : ℕ)^5951*6250000000000^4927 ≤ 2765031804567^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018109577 2000000000 2765031804567 6250000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095176059/2000000000 : ℝ)^5951 ≤ (1932660962437/4000000000000 : ℝ)^4927 := by
    have hnat : (1095176059 : ℕ)^5951*4000000000000^4927 ≤ 1932660962437^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095176059 2000000000 1932660962437 4000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1163822939/10000000000 : ℝ), (1018109577/2000000000 : ℝ), (1095176059/2000000000 : ℝ)] ![(7442967056449/100000000000000 : ℝ), (2765031804567/6250000000000 : ℝ), (1932660962437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1163822939/10000000000 : ℝ)|^5951 ≤ (7442967056449/100000000000000 : ℝ)^4927
        have hw : |(-1163822939/10000000000 : ℝ)|=(1163822939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018109577/2000000000 : ℝ)|^5951 ≤ (2765031804567/6250000000000 : ℝ)^4927
        have hw : |(1018109577/2000000000 : ℝ)|=(1018109577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095176059/2000000000 : ℝ)|^5951 ≤ (1932660962437/4000000000000 : ℝ)^4927
        have hw : |(1095176059/2000000000 : ℝ)|=(1095176059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_5 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044667299/2000000000 : ℝ)*x 0 + (-195944903/2000000000 : ℝ)*x 1 + (1095176059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044667299/2000000000 : ℝ)^5951 ≤ (45638136449601/100000000000000 : ℝ)^4927 := by
    have hnat : (1044667299 : ℕ)^5951*100000000000000^4927 ≤ 45638136449601^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044667299 2000000000 45638136449601 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195944903/2000000000 : ℝ)^5951 ≤ (3022669736473/50000000000000 : ℝ)^4927 := by
    have hnat : (195944903 : ℕ)^5951*50000000000000^4927 ≤ 3022669736473^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195944903 2000000000 3022669736473 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095176059/2000000000 : ℝ)^5951 ≤ (1932660962437/4000000000000 : ℝ)^4927 := by
    have hnat : (1095176059 : ℕ)^5951*4000000000000^4927 ≤ 1932660962437^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095176059 2000000000 1932660962437 4000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044667299/2000000000 : ℝ), (-195944903/2000000000 : ℝ), (1095176059/2000000000 : ℝ)] ![(45638136449601/100000000000000 : ℝ), (3022669736473/50000000000000 : ℝ), (1932660962437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044667299/2000000000 : ℝ)|^5951 ≤ (45638136449601/100000000000000 : ℝ)^4927
        have hw : |(1044667299/2000000000 : ℝ)|=(1044667299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195944903/2000000000 : ℝ)|^5951 ≤ (3022669736473/50000000000000 : ℝ)^4927
        have hw : |(-195944903/2000000000 : ℝ)|=(195944903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095176059/2000000000 : ℝ)|^5951 ≤ (1932660962437/4000000000000 : ℝ)^4927
        have hw : |(1095176059/2000000000 : ℝ)|=(1095176059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_6 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326458531/625000000 : ℝ)*x 0 + (2737940147/5000000000 : ℝ)*x 1 + (-195944903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326458531/625000000 : ℝ)^5951 ≤ (9127627292031/20000000000000 : ℝ)^4927 := by
    have hnat : (326458531 : ℕ)^5951*20000000000000^4927 ≤ 9127627292031^4927*625000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326458531 625000000 9127627292031 20000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737940147/5000000000 : ℝ)^5951 ≤ (48316524050267/100000000000000 : ℝ)^4927 := by
    have hnat : (2737940147 : ℕ)^5951*100000000000000^4927 ≤ 48316524050267^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737940147 5000000000 48316524050267 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195944903/2000000000 : ℝ)^5951 ≤ (3022669736473/50000000000000 : ℝ)^4927 := by
    have hnat : (195944903 : ℕ)^5951*50000000000000^4927 ≤ 3022669736473^4927*2000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195944903 2000000000 3022669736473 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326458531/625000000 : ℝ), (2737940147/5000000000 : ℝ), (-195944903/2000000000 : ℝ)] ![(9127627292031/20000000000000 : ℝ), (48316524050267/100000000000000 : ℝ), (3022669736473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326458531/625000000 : ℝ)|^5951 ≤ (9127627292031/20000000000000 : ℝ)^4927
        have hw : |(326458531/625000000 : ℝ)|=(326458531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737940147/5000000000 : ℝ)|^5951 ≤ (48316524050267/100000000000000 : ℝ)^4927
        have hw : |(2737940147/5000000000 : ℝ)|=(2737940147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195944903/2000000000 : ℝ)|^5951 ≤ (3022669736473/50000000000000 : ℝ)^4927
        have hw : |(-195944903/2000000000 : ℝ)|=(195944903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1761_s2_7 (p : ℝ) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1999899517/5000000000 : ℝ)*x 0 + (4690718487/10000000000 : ℝ)*x 1 + (420964131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999899517/5000000000 : ℝ)^5951 ≤ (33061916173963/100000000000000 : ℝ)^4927 := by
    have hnat : (1999899517 : ℕ)^5951*100000000000000^4927 ≤ 33061916173963^4927*5000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999899517 5000000000 33061916173963 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4690718487/10000000000 : ℝ)^5951 ≤ (20039256835059/50000000000000 : ℝ)^4927 := by
    have hnat : (4690718487 : ℕ)^5951*50000000000000^4927 ≤ 20039256835059^4927*10000000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4690718487 10000000000 20039256835059 50000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420964131/1250000000 : ℝ)^5951 ≤ (26859570139941/100000000000000 : ℝ)^4927 := by
    have hnat : (420964131 : ℕ)^5951*100000000000000^4927 ≤ 26859570139941^4927*1250000000^5951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420964131 1250000000 26859570139941 100000000000000 5951 4927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5951/1024 : ℝ)) 5951 4927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999899517/5000000000 : ℝ), (4690718487/10000000000 : ℝ), (420964131/1250000000 : ℝ)] ![(33061916173963/100000000000000 : ℝ), (20039256835059/50000000000000 : ℝ), (26859570139941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999899517/5000000000 : ℝ)|^5951 ≤ (33061916173963/100000000000000 : ℝ)^4927
        have hw : |(1999899517/5000000000 : ℝ)|=(1999899517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4690718487/10000000000 : ℝ)|^5951 ≤ (20039256835059/50000000000000 : ℝ)^4927
        have hw : |(4690718487/10000000000 : ℝ)|=(4690718487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420964131/1250000000 : ℝ)|^5951 ≤ (26859570139941/100000000000000 : ℝ)^4927
        have hw : |(420964131/1250000000 : ℝ)|=(420964131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1761_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (913/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (913/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (913/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (913/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (913/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (913/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (913/10000 : ℝ) ^ (5935/1024 : ℝ) ≤ (94404827665011/100000000000000000000 : ℝ) := by
    have hpowers : (913/10000 : ℝ)^5935 ≤ (94404827665011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (913 : ℕ)^5935*100000000000000000000^1024 ≤ 94404827665011^1024*10000^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        913 10000 94404827665011 100000000000000000000 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (913/10000 : ℝ)) (X := (94404827665011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17807/100000 : ℝ) ^ (5935/1024 : ℝ) ≤ (2267097268280921/50000000000000000000 : ℝ) := by
    have hpowers : (17807/100000 : ℝ)^5935 ≤ (2267097268280921/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17807 : ℕ)^5935*50000000000000000000^1024 ≤ 2267097268280921^1024*100000^5935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17807 100000 2267097268280921 50000000000000000000 5935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17807/100000 : ℝ)) (X := (2267097268280921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000094404827665011/50000000000000000000 : ℝ) ≤ (2000000651528007/2000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (50000094404827665011/50000000000000000000 : ℝ)^1024 ≤ (2000000651528007/2000000000000000 : ℝ)^5935 := by
      have hnat : (50000094404827665011 : ℕ)^1024*2000000000000000^5935 ≤ 2000000651528007^5935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000094404827665011 50000000000000000000 2000000651528007 2000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000651528007/2000000000000000 : ℝ)) (X := (50000094404827665011/50000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100004628599364226853/100000000000000000000 : ℝ) ≤ (10000079858382251/10000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (100004628599364226853/100000000000000000000 : ℝ)^1024 ≤ (10000079858382251/10000000000000000 : ℝ)^5935 := by
      have hnat : (100004628599364226853 : ℕ)^1024*10000000000000000^5935 ≤ 10000079858382251^5935*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004628599364226853 100000000000000000000 10000079858382251 10000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079858382251/10000000000000000 : ℝ)) (X := (100004628599364226853/100000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002267097268280921/25000000000000000000 : ℝ) ≤ (10000156459124467/10000000000000000 : ℝ) ^ (5935/1024 : ℝ) := by
    have hpowers : (25002267097268280921/25000000000000000000 : ℝ)^1024 ≤ (10000156459124467/10000000000000000 : ℝ)^5935 := by
      have hnat : (25002267097268280921 : ℕ)^1024*10000000000000000^5935 ≤ 10000156459124467^5935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002267097268280921 25000000000000000000 10000156459124467 10000000000000000 1024 5935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000156459124467/10000000000000000 : ℝ)) (X := (25002267097268280921/25000000000000000000 : ℝ)) (by norm_num) 5935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(94404827665011/100000000000000000000 : ℝ) ≤ ((17353725907397943907/17354000000000000000 : ℝ)+2*(9575092777/108462500000000 : ℝ)*(913/10000 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (17353725907397943907/17354000000000000000 : ℝ)+2*(9575092777/108462500000000 : ℝ)*(913/10000 : ℝ)=(2000000651528007/2000000000000000 : ℝ) by norm_num, show 1+2*(94404827665011/100000000000000000000 : ℝ)=(50000094404827665011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2267097268280921/50000000000000000000 : ℝ)+(94404827665011/100000000000000000000 : ℝ) ≤ ((17353725907397943907/17354000000000000000 : ℝ)+(9575092777/108462500000000 : ℝ)*((17807/100000 : ℝ)+(913/10000 : ℝ)))^(5935/1024 : ℝ) := by
    rw [show (17353725907397943907/17354000000000000000 : ℝ)+(9575092777/108462500000000 : ℝ)*((17807/100000 : ℝ)+(913/10000 : ℝ))=(10000079858382251/10000000000000000 : ℝ) by norm_num, show 1+(2267097268280921/50000000000000000000 : ℝ)+(94404827665011/100000000000000000000 : ℝ)=(100004628599364226853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2267097268280921/50000000000000000000 : ℝ) ≤ ((17353725907397943907/17354000000000000000 : ℝ)+2*(9575092777/108462500000000 : ℝ)*(17807/100000 : ℝ))^(5935/1024 : ℝ) := by
    rw [show (17353725907397943907/17354000000000000000 : ℝ)+2*(9575092777/108462500000000 : ℝ)*(17807/100000 : ℝ)=(10000156459124467/10000000000000000 : ℝ) by norm_num, show 1+2*(2267097268280921/50000000000000000000 : ℝ)=(25002267097268280921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17353725907397943907/17354000000000000000 : ℝ)*(X 1 0+X 2 0)+(9575092777/108462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (913/10000 : ℝ)) (hi := (17807/100000 : ℝ)) (c := (17353725907397943907/17354000000000000000 : ℝ)) (alpha := (9575092777/108462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17353725907397943907/17354000000000000000 : ℝ)*(X 0 1+X 2 1)+(9575092777/108462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (913/10000 : ℝ)) (hi := (17807/100000 : ℝ)) (c := (17353725907397943907/17354000000000000000 : ℝ)) (alpha := (9575092777/108462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17353725907397943907/17354000000000000000 : ℝ)*(X 0 2+X 1 2)+(9575092777/108462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5935/1024 : ℝ)) (lo := (913/10000 : ℝ)) (hi := (17807/100000 : ℝ)) (c := (17353725907397943907/17354000000000000000 : ℝ)) (alpha := (9575092777/108462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-232698723/2000000000 : ℝ)*X 0 0+(5482618111/10000000000 : ℝ)*X 0 1+(31774673/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((666081849/1250000000 : ℝ)*X 1 0+(-137165713/1000000000 : ℝ)*X 1 1+(31774673/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((666081849/1250000000 : ℝ)*X 2 0+(31774673/62500000 : ℝ)*X 2 1+(-137165713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((499833541/1250000000 : ℝ)*X 0 0+(3344579341/10000000000 : ℝ)*X 0 1+(4713379717/10000000000 : ℝ)*X 0 2+(499833541/1250000000 : ℝ)*X 1 0+(3344579341/10000000000 : ℝ)*X 1 1+(4713379717/10000000000 : ℝ)*X 1 2+(499833541/1250000000 : ℝ)*X 2 0+(3344579341/10000000000 : ℝ)*X 2 1+(4713379717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1163822939/10000000000 : ℝ)*X 0 0+(1018109577/2000000000 : ℝ)*X 0 1+(1095176059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1044667299/2000000000 : ℝ)*X 1 0+(-195944903/2000000000 : ℝ)*X 1 1+(1095176059/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((326458531/625000000 : ℝ)*X 2 0+(2737940147/5000000000 : ℝ)*X 2 1+(-195944903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1999899517/5000000000 : ℝ)*X 0 0+(4690718487/10000000000 : ℝ)*X 0 1+(420964131/1250000000 : ℝ)*X 0 2+(1999899517/5000000000 : ℝ)*X 1 0+(4690718487/10000000000 : ℝ)*X 1 1+(420964131/1250000000 : ℝ)*X 1 2+(1999899517/5000000000 : ℝ)*X 2 0+(4690718487/10000000000 : ℝ)*X 2 1+(420964131/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1761_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (489672384467417028330649239/108462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (303766353/50000000000000 : ℝ)*(base19) + (574313761/100000000000000 : ℝ)*(base23) + (1770123/10000000000000 : ℝ)*(lower2) + (107544521/100000000000000 : ℝ)*(upper3) + (84098503/100000000000000 : ℝ)*(upper5) + (404864630773741/25000000000000 : ℝ)*(major0) + (404864630773741/25000000000000 : ℝ)*(major1) + (404864630773741/25000000000000 : ℝ)*(major2) + (1254171205622051/50000000000000 : ℝ)*(sp0) + (62708667002603/2500000000000 : ℝ)*(sp1) + (1254173356661533/50000000000000 : ℝ)*(sp2) + (146113613781737/20000000000000 : ℝ)*(sp3) + (1219098181/25000000000000 : ℝ)*(sp4) + (1539155409/100000000000000 : ℝ)*(sp7) + (365284804032047/50000000000000 : ℝ)*(f.failure) + (1254173643818413/50000000000000 : ℝ)*(f.sum) + (61958935079381/10846250000000000000000000000 : ℝ)*base65 + (4013265099132166087/433850000000000000000000000000000 : ℝ)*base67 + (3717451901107216087/433850000000000000000000000000000 : ℝ)*base69 + (67050622237566087/433850000000000000000000000000000 : ℝ)*base71 + (9632049106767/1355781250000000000000000000 : ℝ)*base73 + (800728391366216087/433850000000000000000000000000000 : ℝ)*base75 + (1894388108934366087/433850000000000000000000000000000 : ℝ)*base77 + (2592737529857133913/433850000000000000000000000000000 : ℝ)*base80 + (298142418923379/43385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (52134651/5000000000000000000000 : ℝ)*base90 + (52134651/5000000000000000000000 : ℝ)*base92 + (52134651/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3537584330775731258471328003/867700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51552847/10000000000000 : ℝ)*(base19) + (552197601/100000000000000 : ℝ)*(base23) + (145092357/100000000000000 : ℝ)*(lower1) + (22034723/25000000000000 : ℝ)*(upper3) + (8022563/50000000000000 : ℝ)*(lower4) + (84797961/100000000000000 : ℝ)*(upper5) + (1675505864954681/100000000000000 : ℝ)*(major0) + (1675505864954681/100000000000000 : ℝ)*(major1) + (1675505864954681/100000000000000 : ℝ)*(major2) + (270501801/100000000000000 : ℝ)*(sp2) + (324394740889173/12500000000000 : ℝ)*(sp4) + (1297578705792457/50000000000000 : ℝ)*(sp5) + (2595157104413981/100000000000000 : ℝ)*(sp6) + (94481708362133/12500000000000 : ℝ)*(sp7) + (94481708362133/12500000000000 : ℝ)*(f.failure) + (324394740889173/12500000000000 : ℝ)*(f.sum) + (322001107369/2711562500000000000000000000 : ℝ)*base66 + (3261454947486201333/1735400000000000000000000000000000 : ℝ)*base68 + (4206457202063801333/1735400000000000000000000000000000 : ℝ)*base70 + (19349407063055401333/1735400000000000000000000000000000 : ℝ)*base72 + (110890194733883/21692500000000000000000000000 : ℝ)*base73 + (38247198244853801333/1735400000000000000000000000000000 : ℝ)*base76 + (3219895824300601333/1735400000000000000000000000000000 : ℝ)*base78 + (5915522350877801333/1735400000000000000000000000000000 : ℝ)*base80 + (247338481297201/43385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12847289/1250000000000000000000 : ℝ)*base90 + (12847289/1250000000000000000000 : ℝ)*base92 + (12847289/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1761_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1761_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1761_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17763/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1761_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1761_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1761_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5935/1024 : ℝ) ≤ p) (hpb : p ≤ (5951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (221670667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17763/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1761_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
