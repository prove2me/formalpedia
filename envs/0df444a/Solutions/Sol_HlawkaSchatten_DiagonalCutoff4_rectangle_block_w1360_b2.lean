-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:37.886824+00:00
-- url     : https://prove2.me/submissions/2220386a-0ef6-4215-8f1a-90fde7d9c5d6

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
theorem support_rectangle_w1360_s6_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-253564983/1250000000 : ℝ)*x 0 + (2705893717/5000000000 : ℝ)*x 1 + (5245136841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253564983/1250000000 : ℝ)^135 ≤ (12357595855467/100000000000000 : ℝ)^103 := by
    have hnat : (253564983 : ℕ)^135*100000000000000^103 ≤ 12357595855467^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253564983 1250000000 12357595855467 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705893717/5000000000 : ℝ)^135 ≤ (1397478558063/3125000000000 : ℝ)^103 := by
    have hnat : (2705893717 : ℕ)^135*3125000000000^103 ≤ 1397478558063^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705893717 5000000000 1397478558063 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245136841/10000000000 : ℝ)^135 ≤ (42923090267733/100000000000000 : ℝ)^103 := by
    have hnat : (5245136841 : ℕ)^135*100000000000000^103 ≤ 42923090267733^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245136841 10000000000 42923090267733 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253564983/1250000000 : ℝ), (2705893717/5000000000 : ℝ), (5245136841/10000000000 : ℝ)] ![(12357595855467/100000000000000 : ℝ), (1397478558063/3125000000000 : ℝ), (42923090267733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253564983/1250000000 : ℝ)|^135 ≤ (12357595855467/100000000000000 : ℝ)^103
        have hw : |(-253564983/1250000000 : ℝ)|=(253564983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705893717/5000000000 : ℝ)|^135 ≤ (1397478558063/3125000000000 : ℝ)^103
        have hw : |(2705893717/5000000000 : ℝ)|=(2705893717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245136841/10000000000 : ℝ)|^135 ≤ (42923090267733/100000000000000 : ℝ)^103
        have hw : |(5245136841/10000000000 : ℝ)|=(5245136841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5348682869/10000000000 : ℝ)*x 0 + (-2113415699/10000000000 : ℝ)*x 1 + (2622568187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348682869/10000000000 : ℝ)^135 ≤ (4403709734501/10000000000000 : ℝ)^103 := by
    have hnat : (5348682869 : ℕ)^135*10000000000000^103 ≤ 4403709734501^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348682869 10000000000 4403709734501 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113415699/10000000000 : ℝ)^135 ≤ (13039817375487/100000000000000 : ℝ)^103 := by
    have hnat : (2113415699 : ℕ)^135*100000000000000^103 ≤ 13039817375487^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113415699 10000000000 13039817375487 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622568187/5000000000 : ℝ)^135 ≤ (42923085258773/100000000000000 : ℝ)^103 := by
    have hnat : (2622568187 : ℕ)^135*100000000000000^103 ≤ 42923085258773^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622568187 5000000000 42923085258773 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348682869/10000000000 : ℝ), (-2113415699/10000000000 : ℝ), (2622568187/5000000000 : ℝ)] ![(4403709734501/10000000000000 : ℝ), (13039817375487/100000000000000 : ℝ), (42923085258773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348682869/10000000000 : ℝ)|^135 ≤ (4403709734501/10000000000000 : ℝ)^103
        have hw : |(5348682869/10000000000 : ℝ)|=(5348682869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113415699/10000000000 : ℝ)|^135 ≤ (13039817375487/100000000000000 : ℝ)^103
        have hw : |(-2113415699/10000000000 : ℝ)|=(2113415699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622568187/5000000000 : ℝ)|^135 ≤ (42923085258773/100000000000000 : ℝ)^103
        have hw : |(2622568187/5000000000 : ℝ)|=(2622568187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5348682273/10000000000 : ℝ)*x 0 + (5245136889/10000000000 : ℝ)*x 1 + (-2113415813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348682273/10000000000 : ℝ)^135 ≤ (1761483636539/4000000000000 : ℝ)^103 := by
    have hnat : (5348682273 : ℕ)^135*4000000000000^103 ≤ 1761483636539^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348682273 10000000000 1761483636539 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245136889/10000000000 : ℝ)^135 ≤ (10730772695643/25000000000000 : ℝ)^103 := by
    have hnat : (5245136889 : ℕ)^135*25000000000000^103 ≤ 10730772695643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245136889 10000000000 10730772695643 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113415813/10000000000 : ℝ)^135 ≤ (3259954574349/25000000000000 : ℝ)^103 := by
    have hnat : (2113415813 : ℕ)^135*25000000000000^103 ≤ 3259954574349^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113415813 10000000000 3259954574349 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348682273/10000000000 : ℝ), (5245136889/10000000000 : ℝ), (-2113415813/10000000000 : ℝ)] ![(1761483636539/4000000000000 : ℝ), (10730772695643/25000000000000 : ℝ), (3259954574349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348682273/10000000000 : ℝ)|^135 ≤ (1761483636539/4000000000000 : ℝ)^103
        have hw : |(5348682273/10000000000 : ℝ)|=(5348682273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245136889/10000000000 : ℝ)|^135 ≤ (10730772695643/25000000000000 : ℝ)^103
        have hw : |(5245136889/10000000000 : ℝ)|=(5245136889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113415813/10000000000 : ℝ)|^135 ≤ (3259954574349/25000000000000 : ℝ)^103
        have hw : |(-2113415813/10000000000 : ℝ)|=(2113415813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321933753/10000000000 : ℝ)*x 0 + (4149531911/10000000000 : ℝ)*x 1 + (2250479301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321933753/10000000000 : ℝ)^135 ≤ (8325891168449/25000000000000 : ℝ)^103 := by
    have hnat : (4321933753 : ℕ)^135*25000000000000^103 ≤ 8325891168449^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321933753 10000000000 8325891168449 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149531911/10000000000 : ℝ)^135 ≤ (31573245044851/100000000000000 : ℝ)^103 := by
    have hnat : (4149531911 : ℕ)^135*100000000000000^103 ≤ 31573245044851^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149531911 10000000000 31573245044851 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250479301/5000000000 : ℝ)^135 ≤ (35123190262167/100000000000000 : ℝ)^103 := by
    have hnat : (2250479301 : ℕ)^135*100000000000000^103 ≤ 35123190262167^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250479301 5000000000 35123190262167 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321933753/10000000000 : ℝ), (4149531911/10000000000 : ℝ), (2250479301/5000000000 : ℝ)] ![(8325891168449/25000000000000 : ℝ), (31573245044851/100000000000000 : ℝ), (35123190262167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321933753/10000000000 : ℝ)|^135 ≤ (8325891168449/25000000000000 : ℝ)^103
        have hw : |(4321933753/10000000000 : ℝ)|=(4321933753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149531911/10000000000 : ℝ)|^135 ≤ (31573245044851/100000000000000 : ℝ)^103
        have hw : |(4149531911/10000000000 : ℝ)|=(4149531911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250479301/5000000000 : ℝ)|^135 ≤ (35123190262167/100000000000000 : ℝ)^103
        have hw : |(2250479301/5000000000 : ℝ)|=(2250479301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-63391641/312500000 : ℝ)*x 0 + (5245734199/10000000000 : ℝ)*x 1 + (1352796627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63391641/312500000 : ℝ)^135 ≤ (2471539368869/20000000000000 : ℝ)^103 := by
    have hnat : (63391641 : ℕ)^135*20000000000000^103 ≤ 2471539368869^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63391641 312500000 2471539368869 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245734199/10000000000 : ℝ)^135 ≤ (21464748769193/50000000000000 : ℝ)^103 := by
    have hnat : (5245734199 : ℕ)^135*50000000000000^103 ≤ 21464748769193^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245734199 10000000000 21464748769193 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352796627/2500000000 : ℝ)^135 ≤ (44712805604693/100000000000000 : ℝ)^103 := by
    have hnat : (1352796627 : ℕ)^135*100000000000000^103 ≤ 44712805604693^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352796627 2500000000 44712805604693 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63391641/312500000 : ℝ), (5245734199/10000000000 : ℝ), (1352796627/2500000000 : ℝ)] ![(2471539368869/20000000000000 : ℝ), (21464748769193/50000000000000 : ℝ), (44712805604693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63391641/312500000 : ℝ)|^135 ≤ (2471539368869/20000000000000 : ℝ)^103
        have hw : |(-63391641/312500000 : ℝ)|=(63391641/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245734199/10000000000 : ℝ)|^135 ≤ (21464748769193/50000000000000 : ℝ)^103
        have hw : |(5245734199/10000000000 : ℝ)|=(5245734199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352796627/2500000000 : ℝ)|^135 ≤ (44712805604693/100000000000000 : ℝ)^103
        have hw : |(1352796627/2500000000 : ℝ)|=(1352796627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305669807/10000000000 : ℝ)*x 0 + (-973682621/5000000000 : ℝ)*x 1 + (5411186607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305669807/10000000000 : ℝ)^135 ≤ (8714703431241/20000000000000 : ℝ)^103 := by
    have hnat : (5305669807 : ℕ)^135*20000000000000^103 ≤ 8714703431241^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305669807 10000000000 8714703431241 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973682621/5000000000 : ℝ)^135 ≤ (11713676146093/100000000000000 : ℝ)^103 := by
    have hnat : (973682621 : ℕ)^135*100000000000000^103 ≤ 11713676146093^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973682621 5000000000 11713676146093 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411186607/10000000000 : ℝ)^135 ≤ (22356403338441/50000000000000 : ℝ)^103 := by
    have hnat : (5411186607 : ℕ)^135*50000000000000^103 ≤ 22356403338441^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411186607 10000000000 22356403338441 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305669807/10000000000 : ℝ), (-973682621/5000000000 : ℝ), (5411186607/10000000000 : ℝ)] ![(8714703431241/20000000000000 : ℝ), (11713676146093/100000000000000 : ℝ), (22356403338441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305669807/10000000000 : ℝ)|^135 ≤ (8714703431241/20000000000000 : ℝ)^103
        have hw : |(5305669807/10000000000 : ℝ)|=(5305669807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973682621/5000000000 : ℝ)|^135 ≤ (11713676146093/100000000000000 : ℝ)^103
        have hw : |(-973682621/5000000000 : ℝ)|=(973682621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411186607/10000000000 : ℝ)|^135 ≤ (22356403338441/50000000000000 : ℝ)^103
        have hw : |(5411186607/10000000000 : ℝ)|=(5411186607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (42445357/80000000 : ℝ)*x 0 + (5411186699/10000000000 : ℝ)*x 1 + (-389473073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42445357/80000000 : ℝ)^135 ≤ (21786757598567/50000000000000 : ℝ)^103 := by
    have hnat : (42445357 : ℕ)^135*50000000000000^103 ≤ 21786757598567^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42445357 80000000 21786757598567 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411186699/10000000000 : ℝ)^135 ≤ (44712807673259/100000000000000 : ℝ)^103 := by
    have hnat : (5411186699 : ℕ)^135*100000000000000^103 ≤ 44712807673259^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411186699 10000000000 44712807673259 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389473073/2000000000 : ℝ)^135 ≤ (1464209639477/12500000000000 : ℝ)^103 := by
    have hnat : (389473073 : ℕ)^135*12500000000000^103 ≤ 1464209639477^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389473073 2000000000 1464209639477 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42445357/80000000 : ℝ), (5411186699/10000000000 : ℝ), (-389473073/2000000000 : ℝ)] ![(21786757598567/50000000000000 : ℝ), (44712807673259/100000000000000 : ℝ), (1464209639477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42445357/80000000 : ℝ)|^135 ≤ (21786757598567/50000000000000 : ℝ)^103
        have hw : |(42445357/80000000 : ℝ)|=(42445357/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411186699/10000000000 : ℝ)|^135 ≤ (44712807673259/100000000000000 : ℝ)^103
        have hw : |(5411186699/10000000000 : ℝ)|=(5411186699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389473073/2000000000 : ℝ)|^135 ≤ (1464209639477/12500000000000 : ℝ)^103
        have hw : |(-389473073/2000000000 : ℝ)|=(389473073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s6_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2160979739/5000000000 : ℝ)*x 0 + (899939721/2000000000 : ℝ)*x 1 + (4150797969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160979739/5000000000 : ℝ)^135 ≤ (33303824489229/100000000000000 : ℝ)^103 := by
    have hnat : (2160979739 : ℕ)^135*100000000000000^103 ≤ 33303824489229^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160979739 5000000000 33303824489229 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899939721/2000000000 : ℝ)^135 ≤ (35110303728717/100000000000000 : ℝ)^103 := by
    have hnat : (899939721 : ℕ)^135*100000000000000^103 ≤ 35110303728717^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899939721 2000000000 35110303728717 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150797969/10000000000 : ℝ)^135 ≤ (15792935886623/50000000000000 : ℝ)^103 := by
    have hnat : (4150797969 : ℕ)^135*50000000000000^103 ≤ 15792935886623^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150797969 10000000000 15792935886623 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160979739/5000000000 : ℝ), (899939721/2000000000 : ℝ), (4150797969/10000000000 : ℝ)] ![(33303824489229/100000000000000 : ℝ), (35110303728717/100000000000000 : ℝ), (15792935886623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160979739/5000000000 : ℝ)|^135 ≤ (33303824489229/100000000000000 : ℝ)^103
        have hw : |(2160979739/5000000000 : ℝ)|=(2160979739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899939721/2000000000 : ℝ)|^135 ≤ (35110303728717/100000000000000 : ℝ)^103
        have hw : |(899939721/2000000000 : ℝ)|=(899939721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150797969/10000000000 : ℝ)|^135 ≤ (15792935886623/50000000000000 : ℝ)^103
        have hw : |(4150797969/10000000000 : ℝ)|=(4150797969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1119/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (699/6250 : ℝ) ^ (4319/1024 : ℝ) ≤ (9709533541534073/100000000000000000000 : ℝ) := by
    have hpowers : (699/6250 : ℝ)^4319 ≤ (9709533541534073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (699 : ℕ)^4319*100000000000000000000^1024 ≤ 9709533541534073^1024*6250^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 6250 9709533541534073 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/6250 : ℝ)) (X := (9709533541534073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (4319/1024 : ℝ) ≤ (3872182077365741/12500000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^4319 ≤ (3872182077365741/12500000000000000000 : ℝ)^1024 := by
      have hnat : (589 : ℕ)^4319*12500000000000000000^1024 ≤ 3872182077365741^1024*4000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 3872182077365741 12500000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (3872182077365741/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009709533541534073/50000000000000000000 : ℝ) ≤ (2000092075257579/2000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50009709533541534073/50000000000000000000 : ℝ)^1024 ≤ (2000092075257579/2000000000000000 : ℝ)^4319 := by
      have hnat : (50009709533541534073 : ℕ)^1024*2000000000000000^4319 ≤ 2000092075257579^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009709533541534073 50000000000000000000 2000092075257579 2000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092075257579/2000000000000000 : ℝ)) (X := (50009709533541534073/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040686990160460001/100000000000000000000 : ℝ) ≤ (10000964505978417/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (100040686990160460001/100000000000000000000 : ℝ)^1024 ≤ (10000964505978417/10000000000000000 : ℝ)^4319 := by
      have hnat : (100040686990160460001 : ℕ)^1024*10000000000000000^4319 ≤ 10000964505978417^4319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040686990160460001 100000000000000000000 10000964505978417 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000964505978417/10000000000000000 : ℝ)) (X := (100040686990160460001/100000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253872182077365741/6250000000000000000 : ℝ) ≤ (10001468635668939/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (6253872182077365741/6250000000000000000 : ℝ)^1024 ≤ (10001468635668939/10000000000000000 : ℝ)^4319 := by
      have hnat : (6253872182077365741 : ℕ)^1024*10000000000000000^4319 ≤ 10001468635668939^4319*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253872182077365741 6250000000000000000 10001468635668939 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001468635668939/10000000000000000 : ℝ)) (X := (6253872182077365741/6250000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9709533541534073/100000000000000000000 : ℝ) ≤ ((35400353819517840099/35410000000000000000 : ℝ)+2*(252064845261/177050000000000 : ℝ)*(699/6250 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (35400353819517840099/35410000000000000000 : ℝ)+2*(252064845261/177050000000000 : ℝ)*(699/6250 : ℝ)=(2000092075257579/2000000000000000 : ℝ) by norm_num, show 1+2*(9709533541534073/100000000000000000000 : ℝ)=(50009709533541534073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3872182077365741/12500000000000000000 : ℝ)+(9709533541534073/100000000000000000000 : ℝ) ≤ ((35400353819517840099/35410000000000000000 : ℝ)+(252064845261/177050000000000 : ℝ)*((589/4000 : ℝ)+(699/6250 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (35400353819517840099/35410000000000000000 : ℝ)+(252064845261/177050000000000 : ℝ)*((589/4000 : ℝ)+(699/6250 : ℝ))=(10000964505978417/10000000000000000 : ℝ) by norm_num, show 1+(3872182077365741/12500000000000000000 : ℝ)+(9709533541534073/100000000000000000000 : ℝ)=(100040686990160460001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3872182077365741/12500000000000000000 : ℝ) ≤ ((35400353819517840099/35410000000000000000 : ℝ)+2*(252064845261/177050000000000 : ℝ)*(589/4000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (35400353819517840099/35410000000000000000 : ℝ)+2*(252064845261/177050000000000 : ℝ)*(589/4000 : ℝ)=(10001468635668939/10000000000000000 : ℝ) by norm_num, show 1+2*(3872182077365741/12500000000000000000 : ℝ)=(6253872182077365741/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35400353819517840099/35410000000000000000 : ℝ)*(X 1 0+X 2 0)+(252064845261/177050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (589/4000 : ℝ)) (c := (35400353819517840099/35410000000000000000 : ℝ)) (alpha := (252064845261/177050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35400353819517840099/35410000000000000000 : ℝ)*(X 0 1+X 2 1)+(252064845261/177050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (589/4000 : ℝ)) (c := (35400353819517840099/35410000000000000000 : ℝ)) (alpha := (252064845261/177050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35400353819517840099/35410000000000000000 : ℝ)*(X 0 2+X 1 2)+(252064845261/177050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (589/4000 : ℝ)) (c := (35400353819517840099/35410000000000000000 : ℝ)) (alpha := (252064845261/177050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-253564983/1250000000 : ℝ)*X 0 0+(2705893717/5000000000 : ℝ)*X 0 1+(5245136841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348682869/10000000000 : ℝ)*X 1 0+(-2113415699/10000000000 : ℝ)*X 1 1+(2622568187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348682273/10000000000 : ℝ)*X 2 0+(5245136889/10000000000 : ℝ)*X 2 1+(-2113415813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321933753/10000000000 : ℝ)*X 0 0+(4149531911/10000000000 : ℝ)*X 0 1+(2250479301/5000000000 : ℝ)*X 0 2+(4321933753/10000000000 : ℝ)*X 1 0+(4149531911/10000000000 : ℝ)*X 1 1+(2250479301/5000000000 : ℝ)*X 1 2+(4321933753/10000000000 : ℝ)*X 2 0+(4149531911/10000000000 : ℝ)*X 2 1+(2250479301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-63391641/312500000 : ℝ)*X 0 0+(5245734199/10000000000 : ℝ)*X 0 1+(1352796627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305669807/10000000000 : ℝ)*X 1 0+(-973682621/5000000000 : ℝ)*X 1 1+(5411186607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42445357/80000000 : ℝ)*X 2 0+(5411186699/10000000000 : ℝ)*X 2 1+(-389473073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160979739/5000000000 : ℝ)*X 0 0+(899939721/2000000000 : ℝ)*X 0 1+(4150797969/10000000000 : ℝ)*X 0 2+(2160979739/5000000000 : ℝ)*X 1 0+(899939721/2000000000 : ℝ)*X 1 1+(4150797969/10000000000 : ℝ)*X 1 2+(2160979739/5000000000 : ℝ)*X 2 0+(899939721/2000000000 : ℝ)*X 2 1+(4150797969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8701909669577943560081074941/885250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2286090849/100000000000000 : ℝ)*(base19) + (305813469/20000000000000 : ℝ)*(base23) + (9453917/20000000000000 : ℝ)*(lower2) + (7988957/2000000000000 : ℝ)*(upper3) + (4881021/6250000000000 : ℝ)*(upper5) + (2211553743414551/50000000000000 : ℝ)*(major0) + (2211553743414551/50000000000000 : ℝ)*(major1) + (2211553743414551/50000000000000 : ℝ)*(major2) + (3000309644622729/50000000000000 : ℝ)*(sp0) + (1500160383398153/25000000000000 : ℝ)*(sp1) + (6000642290616117/100000000000000 : ℝ)*(sp2) + (44461810586561/1562500000000 : ℝ)*(sp3) + (6132609501/25000000000000 : ℝ)*(sp4) + (7474385923/50000000000000 : ℝ)*(sp7) + (11382283305247/400000000000 : ℝ)*(f.failure) + (3000321909841731/50000000000000 : ℝ)*(f.sum) + (792878451057/2213125000000000000000000000 : ℝ)*base66 + (21996405320560919451/1770500000000000000000000000000000 : ℝ)*base68 + (22245653212185919451/1770500000000000000000000000000000 : ℝ)*base70 + (22634095133273919451/1770500000000000000000000000000000 : ℝ)*base72 + (18782126310557/8852500000000000000000000000 : ℝ)*base73 + (9278335362584919451/1770500000000000000000000000000000 : ℝ)*base76 + (18060238748340419451/1770500000000000000000000000000000 : ℝ)*base78 + (37641546211433419451/1770500000000000000000000000000000 : ℝ)*base80 + (34772026152761/17705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (813/500000000000000000 : ℝ)*base89 + (813/500000000000000000 : ℝ)*base91 + (813/500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2226435534270294918351953871/442625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9719201/312500000000 : ℝ)*(base19) + (1718854037/50000000000000 : ℝ)*(base23) + (256662949/100000000000000 : ℝ)*(upper2) + (220327571/50000000000000 : ℝ)*(upper3) + (47468559/12500000000000 : ℝ)*(upper5) + (1113771511136343/25000000000000 : ℝ)*(major0) + (1113771511136343/25000000000000 : ℝ)*(major1) + (1113771511136343/25000000000000 : ℝ)*(major2) + (3150757173/5000000000000 : ℝ)*(sp1) + (17330962543/25000000000000 : ℝ)*(sp2) + (6044027945762799/100000000000000 : ℝ)*(sp4) + (302198091023751/5000000000000 : ℝ)*(sp5) + (6043955184204553/100000000000000 : ℝ)*(sp6) + (4478349961967/156250000000 : ℝ)*(sp7) + (4478349961967/156250000000 : ℝ)*(f.failure) + (6044027945762799/100000000000000 : ℝ)*(f.sum) + (12698819965497/2213125000000000000000000000 : ℝ)*base66 + (4281443311669032043/885250000000000000000000000000000 : ℝ)*base68 + (952769750293217957/885250000000000000000000000000000 : ℝ)*base69 + (3087548348763782043/885250000000000000000000000000000 : ℝ)*base72 + (16607928358729/4426250000000000000000000000 : ℝ)*base74 + (5916022468408782043/885250000000000000000000000000000 : ℝ)*base76 + (991361068074032043/885250000000000000000000000000000 : ℝ)*base78 + (9086918373427467957/885250000000000000000000000000000 : ℝ)*base79 + (2753955383689/17705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11/390625000000000000 : ℝ)*base89 + (11/390625000000000000 : ℝ)*base91 + (11/390625000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1360_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s7_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028524399/10000000000 : ℝ)*x 0 + (1352934849/2500000000 : ℝ)*x 1 + (5245181973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028524399/10000000000 : ℝ)^135 ≤ (12357632065483/100000000000000 : ℝ)^103 := by
    have hnat : (2028524399 : ℕ)^135*100000000000000^103 ≤ 12357632065483^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028524399 10000000000 12357632065483 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352934849/2500000000 : ℝ)^135 ≤ (44718793580253/100000000000000 : ℝ)^103 := by
    have hnat : (1352934849 : ℕ)^135*100000000000000^103 ≤ 44718793580253^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352934849 2500000000 44718793580253 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245181973/10000000000 : ℝ)^135 ≤ (42923574346309/100000000000000 : ℝ)^103 := by
    have hnat : (5245181973 : ℕ)^135*100000000000000^103 ≤ 42923574346309^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245181973 10000000000 42923574346309 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028524399/10000000000 : ℝ), (1352934849/2500000000 : ℝ), (5245181973/10000000000 : ℝ)] ![(12357632065483/100000000000000 : ℝ), (44718793580253/100000000000000 : ℝ), (42923574346309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028524399/10000000000 : ℝ)|^135 ≤ (12357632065483/100000000000000 : ℝ)^103
        have hw : |(-2028524399/10000000000 : ℝ)|=(2028524399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352934849/2500000000 : ℝ)|^135 ≤ (44718793580253/100000000000000 : ℝ)^103
        have hw : |(1352934849/2500000000 : ℝ)|=(1352934849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245181973/10000000000 : ℝ)|^135 ≤ (42923574346309/100000000000000 : ℝ)^103
        have hw : |(5245181973/10000000000 : ℝ)|=(5245181973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (267433537/500000000 : ℝ)*x 0 + (-528342873/2500000000 : ℝ)*x 1 + (1311295477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267433537/500000000 : ℝ)^135 ≤ (44036966459001/100000000000000 : ℝ)^103 := by
    have hnat : (267433537 : ℕ)^135*100000000000000^103 ≤ 44036966459001^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267433537 500000000 44036966459001 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528342873/2500000000 : ℝ)^135 ≤ (2607891975639/20000000000000 : ℝ)^103 := by
    have hnat : (528342873 : ℕ)^135*20000000000000^103 ≤ 2607891975639^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528342873 2500000000 2607891975639 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311295477/2500000000 : ℝ)^135 ≤ (5365446706141/12500000000000 : ℝ)^103 := by
    have hnat : (1311295477 : ℕ)^135*12500000000000^103 ≤ 5365446706141^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311295477 2500000000 5365446706141 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267433537/500000000 : ℝ), (-528342873/2500000000 : ℝ), (1311295477/2500000000 : ℝ)] ![(44036966459001/100000000000000 : ℝ), (2607891975639/20000000000000 : ℝ), (5365446706141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267433537/500000000 : ℝ)|^135 ≤ (44036966459001/100000000000000 : ℝ)^103
        have hw : |(267433537/500000000 : ℝ)|=(267433537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528342873/2500000000 : ℝ)|^135 ≤ (2607891975639/20000000000000 : ℝ)^103
        have hw : |(-528342873/2500000000 : ℝ)|=(528342873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311295477/2500000000 : ℝ)|^135 ≤ (5365446706141/12500000000000 : ℝ)^103
        have hw : |(1311295477/2500000000 : ℝ)|=(1311295477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5348670327/10000000000 : ℝ)*x 0 + (5245182203/10000000000 : ℝ)*x 1 + (-528342913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348670327/10000000000 : ℝ)^135 ≤ (44036962002253/100000000000000 : ℝ)^103 := by
    have hnat : (5348670327 : ℕ)^135*100000000000000^103 ≤ 44036962002253^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348670327 10000000000 44036962002253 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245182203/10000000000 : ℝ)^135 ≤ (8584715362651/20000000000000 : ℝ)^103 := by
    have hnat : (5245182203 : ℕ)^135*20000000000000^103 ≤ 8584715362651^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245182203 10000000000 8584715362651 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528342913/2500000000 : ℝ)^135 ≤ (6519730586047/50000000000000 : ℝ)^103 := by
    have hnat : (528342913 : ℕ)^135*50000000000000^103 ≤ 6519730586047^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528342913 2500000000 6519730586047 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348670327/10000000000 : ℝ), (5245182203/10000000000 : ℝ), (-528342913/2500000000 : ℝ)] ![(44036962002253/100000000000000 : ℝ), (8584715362651/20000000000000 : ℝ), (6519730586047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348670327/10000000000 : ℝ)|^135 ≤ (44036962002253/100000000000000 : ℝ)^103
        have hw : |(5348670327/10000000000 : ℝ)|=(5348670327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245182203/10000000000 : ℝ)|^135 ≤ (8584715362651/20000000000000 : ℝ)^103
        have hw : |(5245182203/10000000000 : ℝ)|=(5245182203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528342913/2500000000 : ℝ)|^135 ≤ (6519730586047/50000000000000 : ℝ)^103
        have hw : |(-528342913/2500000000 : ℝ)|=(528342913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321936793/10000000000 : ℝ)*x 0 + (829925897/2000000000 : ℝ)*x 1 + (4500860459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321936793/10000000000 : ℝ)^135 ≤ (4162949422117/12500000000000 : ℝ)^103 := by
    have hnat : (4321936793 : ℕ)^135*12500000000000^103 ≤ 4162949422117^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321936793 10000000000 4162949422117 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829925897/2000000000 : ℝ)^135 ≤ (15787109066687/50000000000000 : ℝ)^103 := by
    have hnat : (829925897 : ℕ)^135*50000000000000^103 ≤ 15787109066687^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829925897 2000000000 15787109066687 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500860459/10000000000 : ℝ)^135 ≤ (35122186471069/100000000000000 : ℝ)^103 := by
    have hnat : (4500860459 : ℕ)^135*100000000000000^103 ≤ 35122186471069^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500860459 10000000000 35122186471069 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321936793/10000000000 : ℝ), (829925897/2000000000 : ℝ), (4500860459/10000000000 : ℝ)] ![(4162949422117/12500000000000 : ℝ), (15787109066687/50000000000000 : ℝ), (35122186471069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321936793/10000000000 : ℝ)|^135 ≤ (4162949422117/12500000000000 : ℝ)^103
        have hw : |(4321936793/10000000000 : ℝ)|=(4321936793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829925897/2000000000 : ℝ)|^135 ≤ (15787109066687/50000000000000 : ℝ)^103
        have hw : |(829925897/2000000000 : ℝ)|=(829925897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500860459/10000000000 : ℝ)|^135 ≤ (35122186471069/100000000000000 : ℝ)^103
        have hw : |(4500860459/10000000000 : ℝ)|=(4500860459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-507134101/2500000000 : ℝ)*x 0 + (1049155777/2000000000 : ℝ)*x 1 + (5411139381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507134101/2500000000 : ℝ)^135 ≤ (6178863960171/50000000000000 : ℝ)^103 := by
    have hnat : (507134101 : ℕ)^135*50000000000000^103 ≤ 6178863960171^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507134101 2500000000 6178863960171 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049155777/2000000000 : ℝ)^135 ≤ (42929976850189/100000000000000 : ℝ)^103 := by
    have hnat : (1049155777 : ℕ)^135*100000000000000^103 ≤ 42929976850189^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049155777 2000000000 42929976850189 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411139381/10000000000 : ℝ)^135 ≤ (44712295211153/100000000000000 : ℝ)^103 := by
    have hnat : (5411139381 : ℕ)^135*100000000000000^103 ≤ 44712295211153^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411139381 10000000000 44712295211153 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507134101/2500000000 : ℝ), (1049155777/2000000000 : ℝ), (5411139381/10000000000 : ℝ)] ![(6178863960171/50000000000000 : ℝ), (42929976850189/100000000000000 : ℝ), (44712295211153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507134101/2500000000 : ℝ)|^135 ≤ (6178863960171/50000000000000 : ℝ)^103
        have hw : |(-507134101/2500000000 : ℝ)|=(507134101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049155777/2000000000 : ℝ)|^135 ≤ (42929976850189/100000000000000 : ℝ)^103
        have hw : |(1049155777/2000000000 : ℝ)|=(1049155777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411139381/10000000000 : ℝ)|^135 ≤ (44712295211153/100000000000000 : ℝ)^103
        have hw : |(5411139381/10000000000 : ℝ)|=(5411139381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1326420337/2500000000 : ℝ)*x 0 + (-389482879/2000000000 : ℝ)*x 1 + (1352784839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326420337/2500000000 : ℝ)^135 ≤ (21786820692537/50000000000000 : ℝ)^103 := by
    have hnat : (1326420337 : ℕ)^135*50000000000000^103 ≤ 21786820692537^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326420337 2500000000 21786820692537 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389482879/2000000000 : ℝ)^135 ≤ (2928515916513/25000000000000 : ℝ)^103 := by
    have hnat : (389482879 : ℕ)^135*25000000000000^103 ≤ 2928515916513^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389482879 2000000000 2928515916513 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352784839/2500000000 : ℝ)^135 ≤ (44712294940399/100000000000000 : ℝ)^103 := by
    have hnat : (1352784839 : ℕ)^135*100000000000000^103 ≤ 44712294940399^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352784839 2500000000 44712294940399 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326420337/2500000000 : ℝ), (-389482879/2000000000 : ℝ), (1352784839/2500000000 : ℝ)] ![(21786820692537/50000000000000 : ℝ), (2928515916513/25000000000000 : ℝ), (44712294940399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326420337/2500000000 : ℝ)|^135 ≤ (21786820692537/50000000000000 : ℝ)^103
        have hw : |(1326420337/2500000000 : ℝ)|=(1326420337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389482879/2000000000 : ℝ)|^135 ≤ (2928515916513/25000000000000 : ℝ)^103
        have hw : |(-389482879/2000000000 : ℝ)|=(389482879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352784839/2500000000 : ℝ)|^135 ≤ (44712294940399/100000000000000 : ℝ)^103
        have hw : |(1352784839/2500000000 : ℝ)|=(1352784839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652840673/5000000000 : ℝ)*x 0 + (270556967/500000000 : ℝ)*x 1 + (-973707209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652840673/5000000000 : ℝ)^135 ≤ (21786820681773/50000000000000 : ℝ)^103 := by
    have hnat : (2652840673 : ℕ)^135*50000000000000^103 ≤ 21786820681773^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652840673 5000000000 21786820681773 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270556967/500000000 : ℝ)^135 ≤ (44712294767117/100000000000000 : ℝ)^103 := by
    have hnat : (270556967 : ℕ)^135*100000000000000^103 ≤ 44712294767117^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270556967 500000000 44712294767117 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973707209/5000000000 : ℝ)^135 ≤ (11714063847383/100000000000000 : ℝ)^103 := by
    have hnat : (973707209 : ℕ)^135*100000000000000^103 ≤ 11714063847383^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973707209 5000000000 11714063847383 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652840673/5000000000 : ℝ), (270556967/500000000 : ℝ), (-973707209/5000000000 : ℝ)] ![(21786820681773/50000000000000 : ℝ), (44712294767117/100000000000000 : ℝ), (11714063847383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652840673/5000000000 : ℝ)|^135 ≤ (21786820681773/50000000000000 : ℝ)^103
        have hw : |(2652840673/5000000000 : ℝ)|=(2652840673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270556967/500000000 : ℝ)|^135 ≤ (44712294767117/100000000000000 : ℝ)^103
        have hw : |(270556967/500000000 : ℝ)|=(270556967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973707209/5000000000 : ℝ)|^135 ≤ (11714063847383/100000000000000 : ℝ)^103
        have hw : |(-973707209/5000000000 : ℝ)|=(973707209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s7_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3376533/7812500 : ℝ)*x 0 + (2249800709/5000000000 : ℝ)*x 1 + (166035793/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3376533/7812500 : ℝ)^135 ≤ (33303852384699/100000000000000 : ℝ)^103 := by
    have hnat : (3376533 : ℕ)^135*100000000000000^103 ≤ 33303852384699^103*7812500^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376533 7812500 33303852384699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249800709/5000000000 : ℝ)^135 ≤ (4388663725233/12500000000000 : ℝ)^103 := by
    have hnat : (2249800709 : ℕ)^135*12500000000000^103 ≤ 4388663725233^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249800709 5000000000 4388663725233 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166035793/400000000 : ℝ)^135 ≤ (6317367558561/20000000000000 : ℝ)^103 := by
    have hnat : (166035793 : ℕ)^135*20000000000000^103 ≤ 6317367558561^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166035793 400000000 6317367558561 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3376533/7812500 : ℝ), (2249800709/5000000000 : ℝ), (166035793/400000000 : ℝ)] ![(33303852384699/100000000000000 : ℝ), (4388663725233/12500000000000 : ℝ), (6317367558561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3376533/7812500 : ℝ)|^135 ≤ (33303852384699/100000000000000 : ℝ)^103
        have hw : |(3376533/7812500 : ℝ)|=(3376533/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249800709/5000000000 : ℝ)|^135 ≤ (4388663725233/12500000000000 : ℝ)^103
        have hw : |(2249800709/5000000000 : ℝ)|=(2249800709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166035793/400000000 : ℝ)|^135 ≤ (6317367558561/20000000000000 : ℝ)^103
        have hw : |(166035793/400000000 : ℝ)|=(166035793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1119/10000 : ℝ) ^ (4319/1024 : ℝ) ≤ (9731522798177887/100000000000000000000 : ℝ) := by
    have hpowers : (1119/10000 : ℝ)^4319 ≤ (9731522798177887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1119 : ℕ)^4319*100000000000000000000^1024 ≤ 9731522798177887^1024*10000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1119 10000 9731522798177887 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1119/10000 : ℝ)) (X := (9731522798177887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14719/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (3865531639423097/12500000000000000000 : ℝ) := by
    have hpowers : (14719/100000 : ℝ)^4319 ≤ (3865531639423097/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14719 : ℕ)^4319*12500000000000000000^1024 ≤ 3865531639423097^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14719 100000 3865531639423097 12500000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14719/100000 : ℝ)) (X := (3865531639423097/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009731522798177887/50000000000000000000 : ℝ) ≤ (2000092283765657/2000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50009731522798177887/50000000000000000000 : ℝ)^1024 ≤ (2000092283765657/2000000000000000 : ℝ)^4319 := by
      have hnat : (50009731522798177887 : ℕ)^1024*2000000000000000^4319 ≤ 2000092283765657^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009731522798177887 50000000000000000000 2000092283765657 2000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092283765657/2000000000000000 : ℝ)) (X := (50009731522798177887/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040655775913562663/100000000000000000000 : ℝ) ≤ (2000192753228679/2000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (100040655775913562663/100000000000000000000 : ℝ)^1024 ≤ (2000192753228679/2000000000000000 : ℝ)^4319 := by
      have hnat : (100040655775913562663 : ℕ)^1024*2000000000000000^4319 ≤ 2000192753228679^4319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040655775913562663 100000000000000000000 2000192753228679 2000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000192753228679/2000000000000000 : ℝ)) (X := (100040655775913562663/100000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253865531639423097/6250000000000000000 : ℝ) ≤ (2000293222691701/2000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (6253865531639423097/6250000000000000000 : ℝ)^1024 ≤ (2000293222691701/2000000000000000 : ℝ)^4319 := by
      have hnat : (6253865531639423097 : ℕ)^1024*2000000000000000^4319 ≤ 2000293222691701^4319*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253865531639423097 6250000000000000000 2000293222691701 2000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000293222691701/2000000000000000 : ℝ)) (X := (6253865531639423097/6250000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9731522798177887/100000000000000000000 : ℝ) ≤ ((7056077162826571193/7058000000000000000 : ℝ)+2*(50234731511/35290000000000 : ℝ)*(1119/10000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (7056077162826571193/7058000000000000000 : ℝ)+2*(50234731511/35290000000000 : ℝ)*(1119/10000 : ℝ)=(2000092283765657/2000000000000000 : ℝ) by norm_num, show 1+2*(9731522798177887/100000000000000000000 : ℝ)=(50009731522798177887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3865531639423097/12500000000000000000 : ℝ)+(9731522798177887/100000000000000000000 : ℝ) ≤ ((7056077162826571193/7058000000000000000 : ℝ)+(50234731511/35290000000000 : ℝ)*((14719/100000 : ℝ)+(1119/10000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (7056077162826571193/7058000000000000000 : ℝ)+(50234731511/35290000000000 : ℝ)*((14719/100000 : ℝ)+(1119/10000 : ℝ))=(2000192753228679/2000000000000000 : ℝ) by norm_num, show 1+(3865531639423097/12500000000000000000 : ℝ)+(9731522798177887/100000000000000000000 : ℝ)=(100040655775913562663/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3865531639423097/12500000000000000000 : ℝ) ≤ ((7056077162826571193/7058000000000000000 : ℝ)+2*(50234731511/35290000000000 : ℝ)*(14719/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (7056077162826571193/7058000000000000000 : ℝ)+2*(50234731511/35290000000000 : ℝ)*(14719/100000 : ℝ)=(2000293222691701/2000000000000000 : ℝ) by norm_num, show 1+2*(3865531639423097/12500000000000000000 : ℝ)=(6253865531639423097/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7056077162826571193/7058000000000000000 : ℝ)*(X 1 0+X 2 0)+(50234731511/35290000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (7056077162826571193/7058000000000000000 : ℝ)) (alpha := (50234731511/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7056077162826571193/7058000000000000000 : ℝ)*(X 0 1+X 2 1)+(50234731511/35290000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (7056077162826571193/7058000000000000000 : ℝ)) (alpha := (50234731511/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7056077162826571193/7058000000000000000 : ℝ)*(X 0 2+X 1 2)+(50234731511/35290000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (7056077162826571193/7058000000000000000 : ℝ)) (alpha := (50234731511/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2028524399/10000000000 : ℝ)*X 0 0+(1352934849/2500000000 : ℝ)*X 0 1+(5245181973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267433537/500000000 : ℝ)*X 1 0+(-528342873/2500000000 : ℝ)*X 1 1+(1311295477/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348670327/10000000000 : ℝ)*X 2 0+(5245182203/10000000000 : ℝ)*X 2 1+(-528342913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321936793/10000000000 : ℝ)*X 0 0+(829925897/2000000000 : ℝ)*X 0 1+(4500860459/10000000000 : ℝ)*X 0 2+(4321936793/10000000000 : ℝ)*X 1 0+(829925897/2000000000 : ℝ)*X 1 1+(4500860459/10000000000 : ℝ)*X 1 2+(4321936793/10000000000 : ℝ)*X 2 0+(829925897/2000000000 : ℝ)*X 2 1+(4500860459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-507134101/2500000000 : ℝ)*X 0 0+(1049155777/2000000000 : ℝ)*X 0 1+(5411139381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326420337/2500000000 : ℝ)*X 1 0+(-389482879/2000000000 : ℝ)*X 1 1+(1352784839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652840673/5000000000 : ℝ)*X 2 0+(270556967/500000000 : ℝ)*X 2 1+(-973707209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3376533/7812500 : ℝ)*X 0 0+(2249800709/5000000000 : ℝ)*X 0 1+(166035793/400000000 : ℝ)*X 0 2+(3376533/7812500 : ℝ)*X 1 0+(2249800709/5000000000 : ℝ)*X 1 1+(166035793/400000000 : ℝ)*X 1 2+(3376533/7812500 : ℝ)*X 2 0+(2249800709/5000000000 : ℝ)*X 2 1+(166035793/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16437014824744148792679/1764500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2123086649/100000000000000 : ℝ)*(base19) + (402851231/25000000000000 : ℝ)*(base23) + (16707137/50000000000000 : ℝ)*(lower2) + (156834927/50000000000000 : ℝ)*(upper3) + (3849451/50000000000000 : ℝ)*(lower4) + (4425602766833321/100000000000000 : ℝ)*(major0) + (4425602766833321/100000000000000 : ℝ)*(major1) + (4425602766833321/100000000000000 : ℝ)*(major2) + (187624671950247/3125000000000 : ℝ)*(sp0) + (6004026955321221/100000000000000 : ℝ)*(sp1) + (3002013733501473/50000000000000 : ℝ)*(sp2) + (711787769502783/25000000000000 : ℝ)*(sp3) + (19787999983/50000000000000 : ℝ)*(sp4) + (195833863/781250000000 : ℝ)*(sp7) + (569435228949119/20000000000000 : ℝ)*(f.failure) + (600402907840787/10000000000000 : ℝ)*(f.sum) + (3324140607571/1764500000000000000000000000 : ℝ)*base66 + (739425234645478047/705800000000000000000000000000000 : ℝ)*base68 + (2492183705026521953/705800000000000000000000000000000 : ℝ)*base69 + (4174360216436521953/705800000000000000000000000000000 : ℝ)*base71 + (5555277037949/1764500000000000000000000000 : ℝ)*base74 + (1803946101347478047/705800000000000000000000000000000 : ℝ)*base76 + (644849101815078047/705800000000000000000000000000000 : ℝ)*base78 + (1543367600919321953/705800000000000000000000000000000 : ℝ)*base79 + (9058208943111/1764500000000000000000000000 : ℝ)*base82 + (35501/25000000000000000000 : ℝ)*base89 + (35501/25000000000000000000 : ℝ)*base91 + (35501/25000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36031595801422083161901/3529000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812421181/100000000000000 : ℝ)*(base19) + (992527797/50000000000000 : ℝ)*(base23) + (153219949/25000000000000 : ℝ)*(lower1) + (50924157/25000000000000 : ℝ)*(upper3) + (10578867/12500000000000 : ℝ)*(lower4) + (22325759/10000000000000 : ℝ)*(upper5) + (1114384712390111/25000000000000 : ℝ)*(major0) + (1114384712390111/25000000000000 : ℝ)*(major1) + (1114384712390111/25000000000000 : ℝ)*(major2) + (950575727/50000000000000 : ℝ)*(sp2) + (188979855957331/3125000000000 : ℝ)*(sp4) + (6047353578213411/100000000000000 : ℝ)*(sp5) + (755918938053443/12500000000000 : ℝ)*(sp6) + (1433860984074083/50000000000000 : ℝ)*(sp7) + (1433860984074083/50000000000000 : ℝ)*(f.failure) + (188979855957331/3125000000000 : ℝ)*(f.sum) + (457168195643/88225000000000000000000000 : ℝ)*base66 + (3660536807078272423/176450000000000000000000000000000 : ℝ)*base67 + (895229129703027577/176450000000000000000000000000000 : ℝ)*base70 + (3567244064266272423/176450000000000000000000000000000 : ℝ)*base71 + (11089979441979/3529000000000000000000000000 : ℝ)*base74 + (19083172090260827577/176450000000000000000000000000000 : ℝ)*base76 + (2051972340582027577/176450000000000000000000000000000 : ℝ)*base78 + (1934473933635372423/176450000000000000000000000000000 : ℝ)*base79 + (4311010559909/1764500000000000000000000000 : ℝ)*base81 + (213257/62500000000000000000 : ℝ)*base89 + (213257/62500000000000000000 : ℝ)*base91 + (213257/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1360_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s8_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1337167097/2500000000 : ℝ)*x 0 + (2622594789/5000000000 : ℝ)*x 1 + (-2113364457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337167097/2500000000 : ℝ)^135 ≤ (22018470539099/50000000000000 : ℝ)^103 := by
    have hnat : (1337167097 : ℕ)^135*50000000000000^103 ≤ 22018470539099^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337167097 2500000000 22018470539099 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622594789/5000000000 : ℝ)^135 ≤ (10730913979111/25000000000000 : ℝ)^103 := by
    have hnat : (2622594789 : ℕ)^135*25000000000000^103 ≤ 10730913979111^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622594789 5000000000 10730913979111 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113364457/10000000000 : ℝ)^135 ≤ (2607880597423/20000000000000 : ℝ)^103 := by
    have hnat : (2113364457 : ℕ)^135*20000000000000^103 ≤ 2607880597423^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113364457 10000000000 2607880597423 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337167097/2500000000 : ℝ), (2622594789/5000000000 : ℝ), (-2113364457/10000000000 : ℝ)] ![(22018470539099/50000000000000 : ℝ), (10730913979111/25000000000000 : ℝ), (2607880597423/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337167097/2500000000 : ℝ)|^135 ≤ (22018470539099/50000000000000 : ℝ)^103
        have hw : |(1337167097/2500000000 : ℝ)|=(1337167097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622594789/5000000000 : ℝ)|^135 ≤ (10730913979111/25000000000000 : ℝ)^103
        have hw : |(2622594789/5000000000 : ℝ)|=(2622594789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113364457/10000000000 : ℝ)|^135 ≤ (2607880597423/20000000000000 : ℝ)^103
        have hw : |(-2113364457/10000000000 : ℝ)|=(2113364457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s8_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4321937457/10000000000 : ℝ)*x 0 + (2074822949/5000000000 : ℝ)*x 1 + (22504219/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321937457/10000000000 : ℝ)^135 ≤ (33303602083149/100000000000000 : ℝ)^103 := by
    have hnat : (4321937457 : ℕ)^135*100000000000000^103 ≤ 33303602083149^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321937457 10000000000 33303602083149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074822949/5000000000 : ℝ)^135 ≤ (15787190909033/50000000000000 : ℝ)^103 := by
    have hnat : (2074822949 : ℕ)^135*50000000000000^103 ≤ 15787190909033^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074822949 5000000000 15787190909033 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22504219/50000000 : ℝ)^135 ≤ (8780504021531/25000000000000 : ℝ)^103 := by
    have hnat : (22504219 : ℕ)^135*25000000000000^103 ≤ 8780504021531^103*50000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22504219 50000000 8780504021531 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321937457/10000000000 : ℝ), (2074822949/5000000000 : ℝ), (22504219/50000000 : ℝ)] ![(33303602083149/100000000000000 : ℝ), (15787190909033/50000000000000 : ℝ), (8780504021531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321937457/10000000000 : ℝ)|^135 ≤ (33303602083149/100000000000000 : ℝ)^103
        have hw : |(4321937457/10000000000 : ℝ)|=(4321937457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2074822949/5000000000 : ℝ)|^135 ≤ (15787190909033/50000000000000 : ℝ)^103
        have hw : |(2074822949/5000000000 : ℝ)|=(2074822949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22504219/50000000 : ℝ)|^135 ≤ (8780504021531/25000000000000 : ℝ)^103
        have hw : |(22504219/50000000 : ℝ)|=(22504219/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s8_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028537097/10000000000 : ℝ)*x 0 + (1311446581/2500000000 : ℝ)*x 1 + (2705565751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028537097/10000000000 : ℝ)^135 ≤ (12357733453659/100000000000000 : ℝ)^103 := by
    have hnat : (2028537097 : ℕ)^135*100000000000000^103 ≤ 12357733453659^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028537097 10000000000 12357733453659 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311446581/2500000000 : ℝ)^135 ≤ (10732514160663/25000000000000 : ℝ)^103 := by
    have hnat : (1311446581 : ℕ)^135*25000000000000^103 ≤ 10732514160663^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311446581 2500000000 10732514160663 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705565751/5000000000 : ℝ)^135 ≤ (44712209880359/100000000000000 : ℝ)^103 := by
    have hnat : (2705565751 : ℕ)^135*100000000000000^103 ≤ 44712209880359^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705565751 5000000000 44712209880359 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028537097/10000000000 : ℝ), (1311446581/2500000000 : ℝ), (2705565751/5000000000 : ℝ)] ![(12357733453659/100000000000000 : ℝ), (10732514160663/25000000000000 : ℝ), (44712209880359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028537097/10000000000 : ℝ)|^135 ≤ (12357733453659/100000000000000 : ℝ)^103
        have hw : |(-2028537097/10000000000 : ℝ)|=(2028537097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311446581/2500000000 : ℝ)|^135 ≤ (10732514160663/25000000000000 : ℝ)^103
        have hw : |(1311446581/2500000000 : ℝ)|=(1311446581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705565751/5000000000 : ℝ)|^135 ≤ (44712209880359/100000000000000 : ℝ)^103
        have hw : |(2705565751/5000000000 : ℝ)|=(2705565751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s8_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652841673/5000000000 : ℝ)*x 0 + (-389484531/2000000000 : ℝ)*x 1 + (5411131357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652841673/5000000000 : ℝ)^135 ≤ (21786831445911/50000000000000 : ℝ)^103 := by
    have hnat : (2652841673 : ℕ)^135*50000000000000^103 ≤ 21786831445911^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652841673 5000000000 21786831445911 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389484531/2000000000 : ℝ)^135 ≤ (2928532196951/25000000000000 : ℝ)^103 := by
    have hnat : (389484531 : ℕ)^135*25000000000000^103 ≤ 2928532196951^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389484531 2000000000 2928532196951 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411131357/10000000000 : ℝ)^135 ≤ (22356104154993/50000000000000 : ℝ)^103 := by
    have hnat : (5411131357 : ℕ)^135*50000000000000^103 ≤ 22356104154993^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411131357 10000000000 22356104154993 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652841673/5000000000 : ℝ), (-389484531/2000000000 : ℝ), (5411131357/10000000000 : ℝ)] ![(21786831445911/50000000000000 : ℝ), (2928532196951/25000000000000 : ℝ), (22356104154993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652841673/5000000000 : ℝ)|^135 ≤ (21786831445911/50000000000000 : ℝ)^103
        have hw : |(2652841673/5000000000 : ℝ)|=(2652841673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389484531/2000000000 : ℝ)|^135 ≤ (2928532196951/25000000000000 : ℝ)^103
        have hw : |(-389484531/2000000000 : ℝ)|=(389484531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411131357/10000000000 : ℝ)|^135 ≤ (22356104154993/50000000000000 : ℝ)^103
        have hw : |(5411131357/10000000000 : ℝ)|=(5411131357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s8_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652841699/5000000000 : ℝ)*x 0 + (541113139/1000000000 : ℝ)*x 1 + (-1947422537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652841699/5000000000 : ℝ)^135 ≤ (43573663451557/100000000000000 : ℝ)^103 := by
    have hnat : (2652841699 : ℕ)^135*100000000000000^103 ≤ 43573663451557^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652841699 5000000000 43573663451557 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541113139/1000000000 : ℝ)^135 ≤ (22356104333691/50000000000000 : ℝ)^103 := by
    have hnat : (541113139 : ℕ)^135*50000000000000^103 ≤ 22356104333691^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541113139 1000000000 22356104333691 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947422537/10000000000 : ℝ)^135 ≤ (11714127857493/100000000000000 : ℝ)^103 := by
    have hnat : (1947422537 : ℕ)^135*100000000000000^103 ≤ 11714127857493^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947422537 10000000000 11714127857493 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652841699/5000000000 : ℝ), (541113139/1000000000 : ℝ), (-1947422537/10000000000 : ℝ)] ![(43573663451557/100000000000000 : ℝ), (22356104333691/50000000000000 : ℝ), (11714127857493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652841699/5000000000 : ℝ)|^135 ≤ (43573663451557/100000000000000 : ℝ)^103
        have hw : |(2652841699/5000000000 : ℝ)|=(2652841699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541113139/1000000000 : ℝ)|^135 ≤ (22356104333691/50000000000000 : ℝ)^103
        have hw : |(541113139/1000000000 : ℝ)|=(541113139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947422537/10000000000 : ℝ)|^135 ≤ (11714127857493/100000000000000 : ℝ)^103
        have hw : |(-1947422537/10000000000 : ℝ)|=(1947422537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s8_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (540245321/1250000000 : ℝ)*x 0 + (449958541/1000000000 : ℝ)*x 1 + (4150910907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540245321/1250000000 : ℝ)^135 ≤ (8325963924353/25000000000000 : ℝ)^103 := by
    have hnat : (540245321 : ℕ)^135*25000000000000^103 ≤ 8325963924353^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540245321 1250000000 8325963924353 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449958541/1000000000 : ℝ)^135 ≤ (8777286522361/25000000000000 : ℝ)^103 := by
    have hnat : (449958541 : ℕ)^135*25000000000000^103 ≤ 8777286522361^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449958541 1000000000 8777286522361 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150910907/10000000000 : ℝ)^135 ≤ (31586998191667/100000000000000 : ℝ)^103 := by
    have hnat : (4150910907 : ℕ)^135*100000000000000^103 ≤ 31586998191667^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150910907 10000000000 31586998191667 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540245321/1250000000 : ℝ), (449958541/1000000000 : ℝ), (4150910907/10000000000 : ℝ)] ![(8325963924353/25000000000000 : ℝ), (8777286522361/25000000000000 : ℝ), (31586998191667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540245321/1250000000 : ℝ)|^135 ≤ (8325963924353/25000000000000 : ℝ)^103
        have hw : |(540245321/1250000000 : ℝ)|=(540245321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449958541/1000000000 : ℝ)|^135 ≤ (8777286522361/25000000000000 : ℝ)^103
        have hw : |(449958541/1000000000 : ℝ)|=(449958541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150910907/10000000000 : ℝ)|^135 ≤ (31586998191667/100000000000000 : ℝ)^103
        have hw : |(4150910907/10000000000 : ℝ)|=(4150910907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11191/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (973519136477431/10000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^4319 ≤ (973519136477431/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11191 : ℕ)^4319*10000000000000000000^1024 ≤ 973519136477431^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 973519136477431 10000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (973519136477431/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7359/50000 : ℝ) ^ (4319/1024 : ℝ) ≤ (30915392646804567/100000000000000000000 : ℝ) := by
    have hpowers : (7359/50000 : ℝ)^4319 ≤ (30915392646804567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7359 : ℕ)^4319*100000000000000000000^1024 ≤ 30915392646804567^1024*50000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7359 50000 30915392646804567 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7359/50000 : ℝ)) (X := (30915392646804567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000973519136477431/5000000000000000000 : ℝ) ≤ (10000461592759953/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (5000973519136477431/5000000000000000000 : ℝ)^1024 ≤ (10000461592759953/10000000000000000 : ℝ)^4319 := by
      have hnat : (5000973519136477431 : ℕ)^1024*10000000000000000^4319 ≤ 10000461592759953^4319*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000973519136477431 5000000000000000000 10000461592759953 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000461592759953/10000000000000000 : ℝ)) (X := (5000973519136477431/5000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040650584011578877/100000000000000000000 : ℝ) ≤ (5000481821542879/5000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (100040650584011578877/100000000000000000000 : ℝ)^1024 ≤ (5000481821542879/5000000000000000 : ℝ)^4319 := by
      have hnat : (100040650584011578877 : ℕ)^1024*5000000000000000^4319 ≤ 5000481821542879^4319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040650584011578877 100000000000000000000 5000481821542879 5000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000481821542879/5000000000000000 : ℝ)) (X := (100040650584011578877/100000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030915392646804567/50000000000000000000 : ℝ) ≤ (10001465693411563/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50030915392646804567/50000000000000000000 : ℝ)^1024 ≤ (10001465693411563/10000000000000000 : ℝ)^4319 := by
      have hnat : (50030915392646804567 : ℕ)^1024*10000000000000000^4319 ≤ 10001465693411563^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030915392646804567 50000000000000000000 10001465693411563 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001465693411563/10000000000000000 : ℝ)) (X := (50030915392646804567/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(973519136477431/10000000000000000000 : ℝ) ≤ ((35260391147272186721/35270000000000000000 : ℝ)+2*(100410065161/70540000000000 : ℝ)*(11191/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (35260391147272186721/35270000000000000000 : ℝ)+2*(100410065161/70540000000000 : ℝ)*(11191/100000 : ℝ)=(10000461592759953/10000000000000000 : ℝ) by norm_num, show 1+2*(973519136477431/10000000000000000000 : ℝ)=(5000973519136477431/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30915392646804567/100000000000000000000 : ℝ)+(973519136477431/10000000000000000000 : ℝ) ≤ ((35260391147272186721/35270000000000000000 : ℝ)+(100410065161/70540000000000 : ℝ)*((7359/50000 : ℝ)+(11191/100000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (35260391147272186721/35270000000000000000 : ℝ)+(100410065161/70540000000000 : ℝ)*((7359/50000 : ℝ)+(11191/100000 : ℝ))=(5000481821542879/5000000000000000 : ℝ) by norm_num, show 1+(30915392646804567/100000000000000000000 : ℝ)+(973519136477431/10000000000000000000 : ℝ)=(100040650584011578877/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30915392646804567/100000000000000000000 : ℝ) ≤ ((35260391147272186721/35270000000000000000 : ℝ)+2*(100410065161/70540000000000 : ℝ)*(7359/50000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (35260391147272186721/35270000000000000000 : ℝ)+2*(100410065161/70540000000000 : ℝ)*(7359/50000 : ℝ)=(10001465693411563/10000000000000000 : ℝ) by norm_num, show 1+2*(30915392646804567/100000000000000000000 : ℝ)=(50030915392646804567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35260391147272186721/35270000000000000000 : ℝ)*(X 1 0+X 2 0)+(100410065161/70540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (35260391147272186721/35270000000000000000 : ℝ)) (alpha := (100410065161/70540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35260391147272186721/35270000000000000000 : ℝ)*(X 0 1+X 2 1)+(100410065161/70540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (35260391147272186721/35270000000000000000 : ℝ)) (alpha := (100410065161/70540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35260391147272186721/35270000000000000000 : ℝ)*(X 0 2+X 1 2)+(100410065161/70540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (35260391147272186721/35270000000000000000 : ℝ)) (alpha := (100410065161/70540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337167097/2500000000 : ℝ)*X 2 0+(2622594789/5000000000 : ℝ)*X 2 1+(-2113364457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4321937457/10000000000 : ℝ)*X 0 0+(2074822949/5000000000 : ℝ)*X 0 1+(22504219/50000000 : ℝ)*X 0 2+(4321937457/10000000000 : ℝ)*X 1 0+(2074822949/5000000000 : ℝ)*X 1 1+(22504219/50000000 : ℝ)*X 1 2+(4321937457/10000000000 : ℝ)*X 2 0+(2074822949/5000000000 : ℝ)*X 2 1+(22504219/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2028537097/10000000000 : ℝ)*X 0 0+(1311446581/2500000000 : ℝ)*X 0 1+(2705565751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652841673/5000000000 : ℝ)*X 1 0+(-389484531/2000000000 : ℝ)*X 1 1+(5411131357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2652841699/5000000000 : ℝ)*X 2 0+(541113139/1000000000 : ℝ)*X 2 1+(-1947422537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((540245321/1250000000 : ℝ)*X 0 0+(449958541/1000000000 : ℝ)*X 0 1+(4150910907/10000000000 : ℝ)*X 0 2+(540245321/1250000000 : ℝ)*X 1 0+(449958541/1000000000 : ℝ)*X 1 1+(4150910907/10000000000 : ℝ)*X 1 2+(540245321/1250000000 : ℝ)*X 2 0+(449958541/1000000000 : ℝ)*X 2 1+(4150910907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1041167673081562578433255029/440875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7016767/3125000000000 : ℝ)*(base19) + (72074129/20000000000000 : ℝ)*(base23) + (3835383/25000000000000 : ℝ)*(lower1) + (17255139/100000000000000 : ℝ)*(lower4) + (2499149/100000000000000 : ℝ)*(lower5) + (1114494828860583/25000000000000 : ℝ)*(major0) + (1114494828860583/25000000000000 : ℝ)*(major1) + (1114494828860583/25000000000000 : ℝ)*(major2) + (5435568591/100000000000000 : ℝ)*(sp0) + (554641639/100000000000000 : ℝ)*(sp1) + (6047953213814337/100000000000000 : ℝ)*(sp2) + (6047952989277793/100000000000000 : ℝ)*(sp3) + (60479474178751/1000000000000 : ℝ)*(sp4) + (2868004783708861/100000000000000 : ℝ)*(sp5) + (5736010676701/200000000000 : ℝ)*(f.failure) + (6047953213814337/100000000000000 : ℝ)*(f.sum) + (11502863540431/1763500000000000000000000000 : ℝ)*base66 + (23121916469950581657/881750000000000000000000000000000 : ℝ)*base68 + (12262095904972331657/881750000000000000000000000000000 : ℝ)*base70 + (43963889249278668343/881750000000000000000000000000000 : ℝ)*base71 + (22371350403307/3527000000000000000000000000 : ℝ)*base74 + (162129714214854581657/881750000000000000000000000000000 : ℝ)*base76 + (15207933490648831657/881750000000000000000000000000000 : ℝ)*base78 + (5255438128031918343/881750000000000000000000000000000 : ℝ)*base79 + (594333779733/220437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2279/250000000000000000 : ℝ)*base89 + (2279/250000000000000000 : ℝ)*base91 + (2279/250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1360_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1360_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1360_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1360_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1360_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
