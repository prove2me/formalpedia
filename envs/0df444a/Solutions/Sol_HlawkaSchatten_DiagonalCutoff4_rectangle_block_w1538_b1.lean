-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1538_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:50.573815+00:00
-- url     : https://prove2.me/submissions/97cadcd5-d092-4810-a887-b953dc7d4cd3

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
theorem support_rectangle_w1538_s3_0 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73196577/400000000 : ℝ)*x 0 + (5432298867/10000000000 : ℝ)*x 1 + (5216659491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73196577/400000000 : ℝ)^4573 ≤ (560516597591/5000000000000 : ℝ)^3549 := by
    have hnat : (73196577 : ℕ)^4573*5000000000000^3549 ≤ 560516597591^3549*400000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73196577 400000000 560516597591 5000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432298867/10000000000 : ℝ)^4573 ≤ (5694137858943/12500000000000 : ℝ)^3549 := by
    have hnat : (5432298867 : ℕ)^4573*12500000000000^3549 ≤ 5694137858943^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432298867 10000000000 5694137858943 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216659491/10000000000 : ℝ)^4573 ≤ (43236565163433/100000000000000 : ℝ)^3549 := by
    have hnat : (5216659491 : ℕ)^4573*100000000000000^3549 ≤ 43236565163433^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216659491 10000000000 43236565163433 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73196577/400000000 : ℝ), (5432298867/10000000000 : ℝ), (5216659491/10000000000 : ℝ)] ![(560516597591/5000000000000 : ℝ), (5694137858943/12500000000000 : ℝ), (43236565163433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73196577/400000000 : ℝ)|^4573 ≤ (560516597591/5000000000000 : ℝ)^3549
        have hw : |(-73196577/400000000 : ℝ)|=(73196577/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432298867/10000000000 : ℝ)|^4573 ≤ (5694137858943/12500000000000 : ℝ)^3549
        have hw : |(5432298867/10000000000 : ℝ)|=(5432298867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216659491/10000000000 : ℝ)|^4573 ≤ (43236565163433/100000000000000 : ℝ)^3549
        have hw : |(5216659491/10000000000 : ℝ)|=(5216659491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_1 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350746817/10000000000 : ℝ)*x 0 + (-970176917/5000000000 : ℝ)*x 1 + (5094394/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350746817/10000000000 : ℝ)^4573 ≤ (44673838637377/100000000000000 : ℝ)^3549 := by
    have hnat : (5350746817 : ℕ)^4573*100000000000000^3549 ≤ 44673838637377^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350746817 10000000000 44673838637377 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970176917/5000000000 : ℝ)^4573 ≤ (1511199569297/12500000000000 : ℝ)^3549 := by
    have hnat : (970176917 : ℕ)^4573*12500000000000^3549 ≤ 1511199569297^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970176917 5000000000 1511199569297 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5094394/9765625 : ℝ)^4573 ≤ (2702285299353/6250000000000 : ℝ)^3549 := by
    have hnat : (5094394 : ℕ)^4573*6250000000000^3549 ≤ 2702285299353^3549*9765625^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094394 9765625 2702285299353 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350746817/10000000000 : ℝ), (-970176917/5000000000 : ℝ), (5094394/9765625 : ℝ)] ![(44673838637377/100000000000000 : ℝ), (1511199569297/12500000000000 : ℝ), (2702285299353/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350746817/10000000000 : ℝ)|^4573 ≤ (44673838637377/100000000000000 : ℝ)^3549
        have hw : |(5350746817/10000000000 : ℝ)|=(5350746817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970176917/5000000000 : ℝ)|^4573 ≤ (1511199569297/12500000000000 : ℝ)^3549
        have hw : |(-970176917/5000000000 : ℝ)|=(970176917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5094394/9765625 : ℝ)|^4573 ≤ (2702285299353/6250000000000 : ℝ)^3549
        have hw : |(5094394/9765625 : ℝ)|=(5094394/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_2 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350746833/10000000000 : ℝ)*x 0 + (1043331889/2000000000 : ℝ)*x 1 + (-1940353829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350746833/10000000000 : ℝ)^4573 ≤ (22336919404753/50000000000000 : ℝ)^3549 := by
    have hnat : (5350746833 : ℕ)^4573*50000000000000^3549 ≤ 22336919404753^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350746833 10000000000 22336919404753 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043331889/2000000000 : ℝ)^4573 ≤ (10809141168043/25000000000000 : ℝ)^3549 := by
    have hnat : (1043331889 : ℕ)^4573*25000000000000^3549 ≤ 10809141168043^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043331889 2000000000 10809141168043 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1940353829/10000000000 : ℝ)^4573 ≤ (6044798257117/50000000000000 : ℝ)^3549 := by
    have hnat : (1940353829 : ℕ)^4573*50000000000000^3549 ≤ 6044798257117^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940353829 10000000000 6044798257117 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350746833/10000000000 : ℝ), (1043331889/2000000000 : ℝ), (-1940353829/10000000000 : ℝ)] ![(22336919404753/50000000000000 : ℝ), (10809141168043/25000000000000 : ℝ), (6044798257117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350746833/10000000000 : ℝ)|^4573 ≤ (22336919404753/50000000000000 : ℝ)^3549
        have hw : |(5350746833/10000000000 : ℝ)|=(5350746833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043331889/2000000000 : ℝ)|^4573 ≤ (10809141168043/25000000000000 : ℝ)^3549
        have hw : |(1043331889/2000000000 : ℝ)|=(1043331889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1940353829/10000000000 : ℝ)|^4573 ≤ (6044798257117/50000000000000 : ℝ)^3549
        have hw : |(-1940353829/10000000000 : ℝ)|=(1940353829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_3 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257585959/10000000000 : ℝ)*x 0 + (1003664791/2500000000 : ℝ)*x 1 + (4512611663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257585959/10000000000 : ℝ)^4573 ≤ (6655722540337/20000000000000 : ℝ)^3549 := by
    have hnat : (4257585959 : ℕ)^4573*20000000000000^3549 ≤ 6655722540337^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257585959 10000000000 6655722540337 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003664791/2500000000 : ℝ)^4573 ≤ (30852378392851/100000000000000 : ℝ)^3549 := by
    have hnat : (1003664791 : ℕ)^4573*100000000000000^3549 ≤ 30852378392851^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003664791 2500000000 30852378392851 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512611663/10000000000 : ℝ)^4573 ≤ (35869008892953/100000000000000 : ℝ)^3549 := by
    have hnat : (4512611663 : ℕ)^4573*100000000000000^3549 ≤ 35869008892953^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512611663 10000000000 35869008892953 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257585959/10000000000 : ℝ), (1003664791/2500000000 : ℝ), (4512611663/10000000000 : ℝ)] ![(6655722540337/20000000000000 : ℝ), (30852378392851/100000000000000 : ℝ), (35869008892953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257585959/10000000000 : ℝ)|^4573 ≤ (6655722540337/20000000000000 : ℝ)^3549
        have hw : |(4257585959/10000000000 : ℝ)|=(4257585959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003664791/2500000000 : ℝ)|^4573 ≤ (30852378392851/100000000000000 : ℝ)^3549
        have hw : |(1003664791/2500000000 : ℝ)|=(1003664791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512611663/10000000000 : ℝ)|^4573 ≤ (35869008892953/100000000000000 : ℝ)^3549
        have hw : |(4512611663/10000000000 : ℝ)|=(4512611663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_4 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914972039/5000000000 : ℝ)*x 0 + (5217799589/10000000000 : ℝ)*x 1 + (2715575141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914972039/5000000000 : ℝ)^4573 ≤ (11210566025481/100000000000000 : ℝ)^3549 := by
    have hnat : (914972039 : ℕ)^4573*100000000000000^3549 ≤ 11210566025481^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914972039 5000000000 11210566025481 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217799589/10000000000 : ℝ)^4573 ≤ (8649748261473/20000000000000 : ℝ)^3549 := by
    have hnat : (5217799589 : ℕ)^4573*20000000000000^3549 ≤ 8649748261473^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217799589 10000000000 8649748261473 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715575141/5000000000 : ℝ)^4573 ≤ (45540692653749/100000000000000 : ℝ)^3549 := by
    have hnat : (2715575141 : ℕ)^4573*100000000000000^3549 ≤ 45540692653749^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715575141 5000000000 45540692653749 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914972039/5000000000 : ℝ), (5217799589/10000000000 : ℝ), (2715575141/5000000000 : ℝ)] ![(11210566025481/100000000000000 : ℝ), (8649748261473/20000000000000 : ℝ), (45540692653749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914972039/5000000000 : ℝ)|^4573 ≤ (11210566025481/100000000000000 : ℝ)^3549
        have hw : |(-914972039/5000000000 : ℝ)|=(914972039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217799589/10000000000 : ℝ)|^4573 ≤ (8649748261473/20000000000000 : ℝ)^3549
        have hw : |(5217799589/10000000000 : ℝ)|=(5217799589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715575141/5000000000 : ℝ)|^4573 ≤ (45540692653749/100000000000000 : ℝ)^3549
        have hw : |(2715575141/5000000000 : ℝ)|=(2715575141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_5 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323481637/2500000000 : ℝ)*x 0 + (-13806903/80000000 : ℝ)*x 1 + (2715575099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323481637/2500000000 : ℝ)^4573 ≤ (8812700290329/20000000000000 : ℝ)^3549 := by
    have hnat : (1323481637 : ℕ)^4573*20000000000000^3549 ≤ 8812700290329^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323481637 2500000000 8812700290329 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13806903/80000000 : ℝ)^4573 ≤ (1039580678799/10000000000000 : ℝ)^3549 := by
    have hnat : (13806903 : ℕ)^4573*10000000000000^3549 ≤ 1039580678799^3549*80000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13806903 80000000 1039580678799 10000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715575099/5000000000 : ℝ)^4573 ≤ (22770345873087/50000000000000 : ℝ)^3549 := by
    have hnat : (2715575099 : ℕ)^4573*50000000000000^3549 ≤ 22770345873087^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715575099 5000000000 22770345873087 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323481637/2500000000 : ℝ), (-13806903/80000000 : ℝ), (2715575099/5000000000 : ℝ)] ![(8812700290329/20000000000000 : ℝ), (1039580678799/10000000000000 : ℝ), (22770345873087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323481637/2500000000 : ℝ)|^4573 ≤ (8812700290329/20000000000000 : ℝ)^3549
        have hw : |(1323481637/2500000000 : ℝ)|=(1323481637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13806903/80000000 : ℝ)|^4573 ≤ (1039580678799/10000000000000 : ℝ)^3549
        have hw : |(-13806903/80000000 : ℝ)|=(13806903/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715575099/5000000000 : ℝ)|^4573 ≤ (22770345873087/50000000000000 : ℝ)^3549
        have hw : |(2715575099/5000000000 : ℝ)|=(2715575099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_6 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293926333/10000000000 : ℝ)*x 0 + (5431150357/10000000000 : ℝ)*x 1 + (-215732869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293926333/10000000000 : ℝ)^4573 ≤ (1762539965831/4000000000000 : ℝ)^3549 := by
    have hnat : (5293926333 : ℕ)^4573*4000000000000^3549 ≤ 1762539965831^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293926333 10000000000 1762539965831 4000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431150357/10000000000 : ℝ)^4573 ≤ (45540693464083/100000000000000 : ℝ)^3549 := by
    have hnat : (5431150357 : ℕ)^4573*100000000000000^3549 ≤ 45540693464083^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431150357 10000000000 45540693464083 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215732869/1250000000 : ℝ)^4573 ≤ (2598951846407/25000000000000 : ℝ)^3549 := by
    have hnat : (215732869 : ℕ)^4573*25000000000000^3549 ≤ 2598951846407^3549*1250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215732869 1250000000 2598951846407 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293926333/10000000000 : ℝ), (5431150357/10000000000 : ℝ), (-215732869/1250000000 : ℝ)] ![(1762539965831/4000000000000 : ℝ), (45540693464083/100000000000000 : ℝ), (2598951846407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293926333/10000000000 : ℝ)|^4573 ≤ (1762539965831/4000000000000 : ℝ)^3549
        have hw : |(5293926333/10000000000 : ℝ)|=(5293926333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431150357/10000000000 : ℝ)|^4573 ≤ (45540693464083/100000000000000 : ℝ)^3549
        have hw : |(5431150357/10000000000 : ℝ)|=(5431150357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215732869/1250000000 : ℝ)|^4573 ≤ (2598951846407/25000000000000 : ℝ)^3549
        have hw : |(-215732869/1250000000 : ℝ)|=(215732869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s3_7 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128827407/5000000000 : ℝ)*x 0 + (2254989563/5000000000 : ℝ)*x 1 + (4017311513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128827407/5000000000 : ℝ)^4573 ≤ (207995663631/625000000000 : ℝ)^3549 := by
    have hnat : (2128827407 : ℕ)^4573*625000000000^3549 ≤ 207995663631^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128827407 5000000000 207995663631 625000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254989563/5000000000 : ℝ)^4573 ≤ (35842048603917/100000000000000 : ℝ)^3549 := by
    have hnat : (2254989563 : ℕ)^4573*100000000000000^3549 ≤ 35842048603917^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254989563 5000000000 35842048603917 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017311513/10000000000 : ℝ)^4573 ≤ (30878645196291/100000000000000 : ℝ)^3549 := by
    have hnat : (4017311513 : ℕ)^4573*100000000000000^3549 ≤ 30878645196291^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017311513 10000000000 30878645196291 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128827407/5000000000 : ℝ), (2254989563/5000000000 : ℝ), (4017311513/10000000000 : ℝ)] ![(207995663631/625000000000 : ℝ), (35842048603917/100000000000000 : ℝ), (30878645196291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128827407/5000000000 : ℝ)|^4573 ≤ (207995663631/625000000000 : ℝ)^3549
        have hw : |(2128827407/5000000000 : ℝ)|=(2128827407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254989563/5000000000 : ℝ)|^4573 ≤ (35842048603917/100000000000000 : ℝ)^3549
        have hw : |(2254989563/5000000000 : ℝ)|=(2254989563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017311513/10000000000 : ℝ)|^4573 ≤ (30878645196291/100000000000000 : ℝ)^3549
        have hw : |(4017311513/10000000000 : ℝ)|=(4017311513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1538_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    (5483/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3107/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (17/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (17/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (17/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (17/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (17/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (17/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (17/160 : ℝ) ^ (4571/1024 : ℝ) ≤ (4504656691303201/100000000000000000000 : ℝ) := by
    have hpowers : (17/160 : ℝ)^4571 ≤ (4504656691303201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17 : ℕ)^4571*100000000000000000000^1024 ≤ 4504656691303201^1024*160^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17 160 4504656691303201 100000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17/160 : ℝ)) (X := (4504656691303201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3181/20000 : ℝ) ^ (4571/1024 : ℝ) ≤ (13637110793325851/50000000000000000000 : ℝ) := by
    have hpowers : (3181/20000 : ℝ)^4571 ≤ (13637110793325851/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3181 : ℕ)^4571*50000000000000000000^1024 ≤ 13637110793325851^1024*20000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3181 20000 13637110793325851 50000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3181/20000 : ℝ)) (X := (13637110793325851/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004504656691303201/50000000000000000000 : ℝ) ≤ (10000201820486559/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50004504656691303201/50000000000000000000 : ℝ)^1024 ≤ (10000201820486559/10000000000000000 : ℝ)^4571 := by
      have hnat : (50004504656691303201 : ℕ)^1024*10000000000000000^4571 ≤ 10000201820486559^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004504656691303201 50000000000000000000 10000201820486559 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000201820486559/10000000000000000 : ℝ)) (X := (50004504656691303201/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031778878277954903/100000000000000000000 : ℝ) ≤ (10000711825853807/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (100031778878277954903/100000000000000000000 : ℝ)^1024 ≤ (10000711825853807/10000000000000000 : ℝ)^4571 := by
      have hnat : (100031778878277954903 : ℕ)^1024*10000000000000000^4571 ≤ 10000711825853807^4571*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031778878277954903 100000000000000000000 10000711825853807 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000711825853807/10000000000000000 : ℝ)) (X := (100031778878277954903/100000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013637110793325851/25000000000000000000 : ℝ) ≤ (2000244366244211/2000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (25013637110793325851/25000000000000000000 : ℝ)^1024 ≤ (2000244366244211/2000000000000000 : ℝ)^4571 := by
      have hnat : (25013637110793325851 : ℕ)^1024*2000000000000000^4571 ≤ 2000244366244211^4571*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013637110793325851 25000000000000000000 2000244366244211 2000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000244366244211/2000000000000000 : ℝ)) (X := (25013637110793325851/25000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4504656691303201/100000000000000000000 : ℝ) ≤ ((164969462494109411/165000000000000000 : ℝ)+2*(31875335453/33000000000000 : ℝ)*(17/160 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (164969462494109411/165000000000000000 : ℝ)+2*(31875335453/33000000000000 : ℝ)*(17/160 : ℝ)=(10000201820486559/10000000000000000 : ℝ) by norm_num, show 1+2*(4504656691303201/100000000000000000000 : ℝ)=(50004504656691303201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13637110793325851/50000000000000000000 : ℝ)+(4504656691303201/100000000000000000000 : ℝ) ≤ ((164969462494109411/165000000000000000 : ℝ)+(31875335453/33000000000000 : ℝ)*((3181/20000 : ℝ)+(17/160 : ℝ)))^(4571/1024 : ℝ) := by
    rw [show (164969462494109411/165000000000000000 : ℝ)+(31875335453/33000000000000 : ℝ)*((3181/20000 : ℝ)+(17/160 : ℝ))=(10000711825853807/10000000000000000 : ℝ) by norm_num, show 1+(13637110793325851/50000000000000000000 : ℝ)+(4504656691303201/100000000000000000000 : ℝ)=(100031778878277954903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13637110793325851/50000000000000000000 : ℝ) ≤ ((164969462494109411/165000000000000000 : ℝ)+2*(31875335453/33000000000000 : ℝ)*(3181/20000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (164969462494109411/165000000000000000 : ℝ)+2*(31875335453/33000000000000 : ℝ)*(3181/20000 : ℝ)=(2000244366244211/2000000000000000 : ℝ) by norm_num, show 1+2*(13637110793325851/50000000000000000000 : ℝ)=(25013637110793325851/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (164969462494109411/165000000000000000 : ℝ)*(X 1 0+X 2 0)+(31875335453/33000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3181/20000 : ℝ)) (c := (164969462494109411/165000000000000000 : ℝ)) (alpha := (31875335453/33000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (164969462494109411/165000000000000000 : ℝ)*(X 0 1+X 2 1)+(31875335453/33000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3181/20000 : ℝ)) (c := (164969462494109411/165000000000000000 : ℝ)) (alpha := (31875335453/33000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (164969462494109411/165000000000000000 : ℝ)*(X 0 2+X 1 2)+(31875335453/33000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3181/20000 : ℝ)) (c := (164969462494109411/165000000000000000 : ℝ)) (alpha := (31875335453/33000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73196577/400000000 : ℝ)*X 0 0+(5432298867/10000000000 : ℝ)*X 0 1+(5216659491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350746817/10000000000 : ℝ)*X 1 0+(-970176917/5000000000 : ℝ)*X 1 1+(5094394/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350746833/10000000000 : ℝ)*X 2 0+(1043331889/2000000000 : ℝ)*X 2 1+(-1940353829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4257585959/10000000000 : ℝ)*X 0 0+(1003664791/2500000000 : ℝ)*X 0 1+(4512611663/10000000000 : ℝ)*X 0 2+(4257585959/10000000000 : ℝ)*X 1 0+(1003664791/2500000000 : ℝ)*X 1 1+(4512611663/10000000000 : ℝ)*X 1 2+(4257585959/10000000000 : ℝ)*X 2 0+(1003664791/2500000000 : ℝ)*X 2 1+(4512611663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-914972039/5000000000 : ℝ)*X 0 0+(5217799589/10000000000 : ℝ)*X 0 1+(2715575141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323481637/2500000000 : ℝ)*X 1 0+(-13806903/80000000 : ℝ)*X 1 1+(2715575099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293926333/10000000000 : ℝ)*X 2 0+(5431150357/10000000000 : ℝ)*X 2 1+(-215732869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2128827407/5000000000 : ℝ)*X 0 0+(2254989563/5000000000 : ℝ)*X 0 1+(4017311513/10000000000 : ℝ)*X 0 2+(2128827407/5000000000 : ℝ)*X 1 0+(2254989563/5000000000 : ℝ)*X 1 1+(4017311513/10000000000 : ℝ)*X 1 2+(2128827407/5000000000 : ℝ)*X 2 0+(2254989563/5000000000 : ℝ)*X 2 1+(4017311513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102476434599815180467/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29760827/4000000000000 : ℝ)*(base19) + (362761973/50000000000000 : ℝ)*(base23) + (8658481/50000000000000 : ℝ)*(lower2) + (22977197/25000000000000 : ℝ)*(upper3) + (75999229/100000000000000 : ℝ)*(upper5) + (830703612936527/25000000000000 : ℝ)*(major0) + (830703612936527/25000000000000 : ℝ)*(major1) + (830703612936527/25000000000000 : ℝ)*(major2) + (4637383498766889/100000000000000 : ℝ)*(sp0) + (4637394305393903/100000000000000 : ℝ)*(sp1) + (579674290486329/12500000000000 : ℝ)*(sp2) + (2008228524161127/100000000000000 : ℝ)*(sp3) + (11550647689/100000000000000 : ℝ)*(sp4) + (259664063/5000000000000 : ℝ)*(sp7) + (2008233717442387/100000000000000 : ℝ)*(f.failure) + (2318697524707289/50000000000000 : ℝ)*(f.sum) + (114654084227/18750000000000000000000000 : ℝ)*base66 + (545559506379109/125000000000000000000000000000 : ℝ)*base67 + (62509394370891/125000000000000000000000000000 : ℝ)*base70 + (445858870120891/125000000000000000000000000000 : ℝ)*base72 + (1932606511/585937500000000000000000 : ℝ)*base74 + (662952484254109/125000000000000000000000000000 : ℝ)*base75 + (821347833245891/125000000000000000000000000000 : ℝ)*base78 + (1394308924379109/125000000000000000000000000000 : ℝ)*base79 + (78552504067/75000000000000000000000000 : ℝ)*base81 + (13496537/10000000000000000000000 : ℝ)*base90 + (13496537/10000000000000000000000 : ℝ)*base92 + (13496537/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16991486181287836654077/2685546875000000000000000000 : ℝ) := by norm_num
    linear_combination (276096927/25000000000000 : ℝ)*(base19) + (226473607/20000000000000 : ℝ)*(base23) + (53329161/50000000000000 : ℝ)*(upper3) + (108068259/100000000000000 : ℝ)*(lower4) + (46083769/50000000000000 : ℝ)*(upper5) + (419805031666623/12500000000000 : ℝ)*(major0) + (419805031666623/12500000000000 : ℝ)*(major1) + (419805031666623/12500000000000 : ℝ)*(major2) + (8358124521/50000000000000 : ℝ)*(sp1) + (360783341/2000000000000 : ℝ)*(sp2) + (4687115151577379/100000000000000 : ℝ)*(sp4) + (1171774332735157/25000000000000 : ℝ)*(sp5) + (4687095980042293/100000000000000 : ℝ)*(sp6) + (1014882572094097/50000000000000 : ℝ)*(sp7) + (1014882572094097/50000000000000 : ℝ)*(f.failure) + (4687115151577379/100000000000000 : ℝ)*(f.sum) + (990834183529/137500000000000000000000000 : ℝ)*base66 + (9858859654901149/687500000000000000000000000000 : ℝ)*base68 + (4793024653338649/687500000000000000000000000000 : ℝ)*base70 + (2630018322963649/687500000000000000000000000000 : ℝ)*base72 + (63207690413/17187500000000000000000000 : ℝ)*base74 + (6434784703213649/687500000000000000000000000000 : ℝ)*base76 + (5428186471151149/687500000000000000000000000000 : ℝ)*base78 + (474651293848851/687500000000000000000000000000 : ℝ)*base79 + (29887451777/68750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (75182253/5000000000000000000000 : ℝ)*base89 + (75182253/5000000000000000000000 : ℝ)*base91 + (75182253/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1538_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1538_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1538_s4_0 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1830239087/10000000000 : ℝ)*x 0 + (1357534789/2500000000 : ℝ)*x 1 + (2609302191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1830239087/10000000000 : ℝ)^4573 ≤ (140161185191/1250000000000 : ℝ)^3549 := by
    have hnat : (1830239087 : ℕ)^4573*1250000000000^3549 ≤ 140161185191^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830239087 10000000000 140161185191 1250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357534789/2500000000 : ℝ)^4573 ≤ (5691221034759/12500000000000 : ℝ)^3549 := by
    have hnat : (1357534789 : ℕ)^4573*12500000000000^3549 ≤ 5691221034759^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357534789 2500000000 5691221034759 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609302191/5000000000 : ℝ)^4573 ≤ (43257336886319/100000000000000 : ℝ)^3549 := by
    have hnat : (2609302191 : ℕ)^4573*100000000000000^3549 ≤ 43257336886319^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609302191 5000000000 43257336886319 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1830239087/10000000000 : ℝ), (1357534789/2500000000 : ℝ), (2609302191/5000000000 : ℝ)] ![(140161185191/1250000000000 : ℝ), (5691221034759/12500000000000 : ℝ), (43257336886319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1830239087/10000000000 : ℝ)|^4573 ≤ (140161185191/1250000000000 : ℝ)^3549
        have hw : |(-1830239087/10000000000 : ℝ)|=(1830239087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357534789/2500000000 : ℝ)|^4573 ≤ (5691221034759/12500000000000 : ℝ)^3549
        have hw : |(1357534789/2500000000 : ℝ)|=(1357534789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609302191/5000000000 : ℝ)|^4573 ≤ (43257336886319/100000000000000 : ℝ)^3549
        have hw : |(2609302191/5000000000 : ℝ)|=(2609302191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_1 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350178489/10000000000 : ℝ)*x 0 + (-1938528411/10000000000 : ℝ)*x 1 + (5218603919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350178489/10000000000 : ℝ)^4573 ≤ (11166931155701/25000000000000 : ℝ)^3549 := by
    have hnat : (5350178489 : ℕ)^4573*25000000000000^3549 ≤ 11166931155701^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350178489 10000000000 11166931155701 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938528411/10000000000 : ℝ)^4573 ≤ (12074943416523/100000000000000 : ℝ)^3549 := by
    have hnat : (1938528411 : ℕ)^4573*100000000000000^3549 ≤ 12074943416523^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938528411 10000000000 12074943416523 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218603919/10000000000 : ℝ)^4573 ≤ (5407166492643/12500000000000 : ℝ)^3549 := by
    have hnat : (5218603919 : ℕ)^4573*12500000000000^3549 ≤ 5407166492643^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218603919 10000000000 5407166492643 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350178489/10000000000 : ℝ), (-1938528411/10000000000 : ℝ), (5218603919/10000000000 : ℝ)] ![(11166931155701/25000000000000 : ℝ), (12074943416523/100000000000000 : ℝ), (5407166492643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350178489/10000000000 : ℝ)|^4573 ≤ (11166931155701/25000000000000 : ℝ)^3549
        have hw : |(5350178489/10000000000 : ℝ)|=(5350178489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938528411/10000000000 : ℝ)|^4573 ≤ (12074943416523/100000000000000 : ℝ)^3549
        have hw : |(-1938528411/10000000000 : ℝ)|=(1938528411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218603919/10000000000 : ℝ)|^4573 ≤ (5407166492643/12500000000000 : ℝ)^3549
        have hw : |(5218603919/10000000000 : ℝ)|=(5218603919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_2 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350178279/10000000000 : ℝ)*x 0 + (5218604241/10000000000 : ℝ)*x 1 + (-387705653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350178279/10000000000 : ℝ)^4573 ≤ (279173264773/625000000000 : ℝ)^3549 := by
    have hnat : (5350178279 : ℕ)^4573*625000000000^3549 ≤ 279173264773^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350178279 10000000000 279173264773 625000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218604241/10000000000 : ℝ)^4573 ≤ (43257335380337/100000000000000 : ℝ)^3549 := by
    have hnat : (5218604241 : ℕ)^4573*100000000000000^3549 ≤ 43257335380337^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218604241 10000000000 43257335380337 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387705653/2000000000 : ℝ)^4573 ≤ (12074942244703/100000000000000 : ℝ)^3549 := by
    have hnat : (387705653 : ℕ)^4573*100000000000000^3549 ≤ 12074942244703^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387705653 2000000000 12074942244703 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350178279/10000000000 : ℝ), (5218604241/10000000000 : ℝ), (-387705653/2000000000 : ℝ)] ![(279173264773/625000000000 : ℝ), (43257335380337/100000000000000 : ℝ), (12074942244703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350178279/10000000000 : ℝ)|^4573 ≤ (279173264773/625000000000 : ℝ)^3549
        have hw : |(5350178279/10000000000 : ℝ)|=(5350178279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218604241/10000000000 : ℝ)|^4573 ≤ (43257335380337/100000000000000 : ℝ)^3549
        have hw : |(5218604241/10000000000 : ℝ)|=(5218604241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387705653/2000000000 : ℝ)|^4573 ≤ (12074942244703/100000000000000 : ℝ)^3549
        have hw : |(-387705653/2000000000 : ℝ)|=(387705653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_3 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532223911/1250000000 : ℝ)*x 0 + (401937391/1000000000 : ℝ)*x 1 + (4507849911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532223911/1250000000 : ℝ)^4573 ≤ (8320170175147/25000000000000 : ℝ)^3549 := by
    have hnat : (532223911 : ℕ)^4573*25000000000000^3549 ≤ 8320170175147^3549*1250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532223911 1250000000 8320170175147 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401937391/1000000000 : ℝ)^4573 ≤ (3089907303209/10000000000000 : ℝ)^3549 := by
    have hnat : (401937391 : ℕ)^4573*10000000000000^3549 ≤ 3089907303209^3549*1000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401937391 1000000000 3089907303209 10000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507849911/10000000000 : ℝ)^4573 ≤ (35820246247867/100000000000000 : ℝ)^3549 := by
    have hnat : (4507849911 : ℕ)^4573*100000000000000^3549 ≤ 35820246247867^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507849911 10000000000 35820246247867 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532223911/1250000000 : ℝ), (401937391/1000000000 : ℝ), (4507849911/10000000000 : ℝ)] ![(8320170175147/25000000000000 : ℝ), (3089907303209/10000000000000 : ℝ), (35820246247867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532223911/1250000000 : ℝ)|^4573 ≤ (8320170175147/25000000000000 : ℝ)^3549
        have hw : |(532223911/1250000000 : ℝ)|=(532223911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401937391/1000000000 : ℝ)|^4573 ≤ (3089907303209/10000000000000 : ℝ)^3549
        have hw : |(401937391/1000000000 : ℝ)|=(401937391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507849911/10000000000 : ℝ)|^4573 ≤ (35820246247867/100000000000000 : ℝ)^3549
        have hw : |(4507849911/10000000000 : ℝ)|=(4507849911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_4 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-915133813/5000000000 : ℝ)*x 0 + (1043940133/2000000000 : ℝ)*x 1 + (1357258613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915133813/5000000000 : ℝ)^4573 ≤ (2803280026701/25000000000000 : ℝ)^3549 := by
    have hnat : (915133813 : ℕ)^4573*25000000000000^3549 ≤ 2803280026701^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915133813 5000000000 2803280026701 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043940133/2000000000 : ℝ)^4573 ≤ (2163452316749/5000000000000 : ℝ)^3549 := by
    have hnat : (1043940133 : ℕ)^4573*5000000000000^3549 ≤ 2163452316749^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043940133 2000000000 2163452316749 5000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357258613/2500000000 : ℝ)^4573 ≤ (2275891677041/5000000000000 : ℝ)^3549 := by
    have hnat : (1357258613 : ℕ)^4573*5000000000000^3549 ≤ 2275891677041^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357258613 2500000000 2275891677041 5000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-915133813/5000000000 : ℝ), (1043940133/2000000000 : ℝ), (1357258613/2500000000 : ℝ)] ![(2803280026701/25000000000000 : ℝ), (2163452316749/5000000000000 : ℝ), (2275891677041/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-915133813/5000000000 : ℝ)|^4573 ≤ (2803280026701/25000000000000 : ℝ)^3549
        have hw : |(-915133813/5000000000 : ℝ)|=(915133813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043940133/2000000000 : ℝ)|^4573 ≤ (2163452316749/5000000000000 : ℝ)^3549
        have hw : |(1043940133/2000000000 : ℝ)|=(1043940133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357258613/2500000000 : ℝ)|^4573 ≤ (2275891677041/5000000000000 : ℝ)^3549
        have hw : |(1357258613/2500000000 : ℝ)|=(1357258613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_5 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058887993/2000000000 : ℝ)*x 0 + (-1728098437/10000000000 : ℝ)*x 1 + (2714517093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058887993/2000000000 : ℝ)^4573 ≤ (2754312994579/6250000000000 : ℝ)^3549 := by
    have hnat : (1058887993 : ℕ)^4573*6250000000000^3549 ≤ 2754312994579^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058887993 2000000000 2754312994579 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1728098437/10000000000 : ℝ)^4573 ≤ (5206580700993/50000000000000 : ℝ)^3549 := by
    have hnat : (1728098437 : ℕ)^4573*50000000000000^3549 ≤ 5206580700993^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728098437 10000000000 5206580700993 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714517093/5000000000 : ℝ)^4573 ≤ (45517830667157/100000000000000 : ℝ)^3549 := by
    have hnat : (2714517093 : ℕ)^4573*100000000000000^3549 ≤ 45517830667157^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714517093 5000000000 45517830667157 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058887993/2000000000 : ℝ), (-1728098437/10000000000 : ℝ), (2714517093/5000000000 : ℝ)] ![(2754312994579/6250000000000 : ℝ), (5206580700993/50000000000000 : ℝ), (45517830667157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058887993/2000000000 : ℝ)|^4573 ≤ (2754312994579/6250000000000 : ℝ)^3549
        have hw : |(1058887993/2000000000 : ℝ)|=(1058887993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1728098437/10000000000 : ℝ)|^4573 ≤ (5206580700993/50000000000000 : ℝ)^3549
        have hw : |(-1728098437/10000000000 : ℝ)|=(1728098437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714517093/5000000000 : ℝ)|^4573 ≤ (45517830667157/100000000000000 : ℝ)^3549
        have hw : |(2714517093/5000000000 : ℝ)|=(2714517093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_6 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294440557/10000000000 : ℝ)*x 0 + (1085806787/2000000000 : ℝ)*x 1 + (-1728097969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294440557/10000000000 : ℝ)^4573 ≤ (44069014262627/100000000000000 : ℝ)^3549 := by
    have hnat : (5294440557 : ℕ)^4573*100000000000000^3549 ≤ 44069014262627^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294440557 10000000000 44069014262627 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085806787/2000000000 : ℝ)^4573 ≤ (45517827955543/100000000000000 : ℝ)^3549 := by
    have hnat : (1085806787 : ℕ)^4573*100000000000000^3549 ≤ 45517827955543^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085806787 2000000000 45517827955543 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1728097969/10000000000 : ℝ)^4573 ≤ (2082631553647/20000000000000 : ℝ)^3549 := by
    have hnat : (1728097969 : ℕ)^4573*20000000000000^3549 ≤ 2082631553647^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728097969 10000000000 2082631553647 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294440557/10000000000 : ℝ), (1085806787/2000000000 : ℝ), (-1728097969/10000000000 : ℝ)] ![(44069014262627/100000000000000 : ℝ), (45517827955543/100000000000000 : ℝ), (2082631553647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294440557/10000000000 : ℝ)|^4573 ≤ (44069014262627/100000000000000 : ℝ)^3549
        have hw : |(5294440557/10000000000 : ℝ)|=(5294440557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085806787/2000000000 : ℝ)|^4573 ≤ (45517827955543/100000000000000 : ℝ)^3549
        have hw : |(1085806787/2000000000 : ℝ)|=(1085806787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1728097969/10000000000 : ℝ)|^4573 ≤ (2082631553647/20000000000000 : ℝ)^3549
        have hw : |(-1728097969/10000000000 : ℝ)|=(1728097969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s4_7 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257855911/10000000000 : ℝ)*x 0 + (450531663/1000000000 : ℝ)*x 1 + (160877051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257855911/10000000000 : ℝ)^4573 ≤ (1664066578293/5000000000000 : ℝ)^3549 := by
    have hnat : (4257855911 : ℕ)^4573*5000000000000^3549 ≤ 1664066578293^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257855911 10000000000 1664066578293 5000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450531663/1000000000 : ℝ)^4573 ≤ (7158862055857/20000000000000 : ℝ)^3549 := by
    have hnat : (450531663 : ℕ)^4573*20000000000000^3549 ≤ 7158862055857^3549*1000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450531663 1000000000 7158862055857 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160877051/400000000 : ℝ)^4573 ≤ (15462179069747/50000000000000 : ℝ)^3549 := by
    have hnat : (160877051 : ℕ)^4573*50000000000000^3549 ≤ 15462179069747^3549*400000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160877051 400000000 15462179069747 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257855911/10000000000 : ℝ), (450531663/1000000000 : ℝ), (160877051/400000000 : ℝ)] ![(1664066578293/5000000000000 : ℝ), (7158862055857/20000000000000 : ℝ), (15462179069747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257855911/10000000000 : ℝ)|^4573 ≤ (1664066578293/5000000000000 : ℝ)^3549
        have hw : |(4257855911/10000000000 : ℝ)|=(4257855911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450531663/1000000000 : ℝ)|^4573 ≤ (7158862055857/20000000000000 : ℝ)^3549
        have hw : |(450531663/1000000000 : ℝ)|=(450531663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160877051/400000000 : ℝ)|^4573 ≤ (15462179069747/50000000000000 : ℝ)^3549
        have hw : |(160877051/400000000 : ℝ)|=(160877051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1538_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11007/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3107/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5483/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3107/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5483/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3107/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5483/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3107/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5483/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3107/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5483/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3107/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5483/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5483/50000 : ℝ) ^ (4571/1024 : ℝ) ≤ (5186839910091507/100000000000000000000 : ℝ) := by
    have hpowers : (5483/50000 : ℝ)^4571 ≤ (5186839910091507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5483 : ℕ)^4571*100000000000000000000^1024 ≤ 5186839910091507^1024*50000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5483 50000 5186839910091507 100000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5483/50000 : ℝ)) (X := (5186839910091507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3107/20000 : ℝ) ^ (4571/1024 : ℝ) ≤ (4910784241314299/20000000000000000000 : ℝ) := by
    have hpowers : (3107/20000 : ℝ)^4571 ≤ (4910784241314299/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3107 : ℕ)^4571*20000000000000000000^1024 ≤ 4910784241314299^1024*20000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3107 20000 4910784241314299 20000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3107/20000 : ℝ)) (X := (4910784241314299/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005186839910091507/50000000000000000000 : ℝ) ≤ (2500058095715453/2500000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50005186839910091507/50000000000000000000 : ℝ)^1024 ≤ (2500058095715453/2500000000000000 : ℝ)^4571 := by
      have hnat : (50005186839910091507 : ℕ)^1024*2500000000000000^4571 ≤ 2500058095715453^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005186839910091507 50000000000000000000 2500058095715453 2500000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500058095715453/2500000000000000 : ℝ)) (X := (50005186839910091507/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014870380558331501/50000000000000000000 : ℝ) ≤ (10000666178644091/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50014870380558331501/50000000000000000000 : ℝ)^1024 ≤ (10000666178644091/10000000000000000 : ℝ)^4571 := by
      have hnat : (50014870380558331501 : ℕ)^1024*10000000000000000^4571 ≤ 10000666178644091^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014870380558331501 50000000000000000000 10000666178644091 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666178644091/10000000000000000 : ℝ)) (X := (50014870380558331501/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004910784241314299/10000000000000000000 : ℝ) ≤ (1000109997442637/1000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (10004910784241314299/10000000000000000000 : ℝ)^1024 ≤ (1000109997442637/1000000000000000 : ℝ)^4571 := by
      have hnat : (10004910784241314299 : ℕ)^1024*1000000000000000^4571 ≤ 1000109997442637^4571*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004910784241314299 10000000000000000000 1000109997442637 1000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000109997442637/1000000000000000 : ℝ)) (X := (10004910784241314299/10000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5186839910091507/100000000000000000000 : ℝ) ≤ ((3806795645683223/3807500000000000 : ℝ)+2*(144598594093/152300000000000 : ℝ)*(5483/50000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (3806795645683223/3807500000000000 : ℝ)+2*(144598594093/152300000000000 : ℝ)*(5483/50000 : ℝ)=(2500058095715453/2500000000000000 : ℝ) by norm_num, show 1+2*(5186839910091507/100000000000000000000 : ℝ)=(50005186839910091507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4910784241314299/20000000000000000000 : ℝ)+(5186839910091507/100000000000000000000 : ℝ) ≤ ((3806795645683223/3807500000000000 : ℝ)+(144598594093/152300000000000 : ℝ)*((3107/20000 : ℝ)+(5483/50000 : ℝ)))^(4571/1024 : ℝ) := by
    rw [show (3806795645683223/3807500000000000 : ℝ)+(144598594093/152300000000000 : ℝ)*((3107/20000 : ℝ)+(5483/50000 : ℝ))=(10000666178644091/10000000000000000 : ℝ) by norm_num, show 1+(4910784241314299/20000000000000000000 : ℝ)+(5186839910091507/100000000000000000000 : ℝ)=(50014870380558331501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4910784241314299/20000000000000000000 : ℝ) ≤ ((3806795645683223/3807500000000000 : ℝ)+2*(144598594093/152300000000000 : ℝ)*(3107/20000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (3806795645683223/3807500000000000 : ℝ)+2*(144598594093/152300000000000 : ℝ)*(3107/20000 : ℝ)=(1000109997442637/1000000000000000 : ℝ) by norm_num, show 1+2*(4910784241314299/20000000000000000000 : ℝ)=(10004910784241314299/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3806795645683223/3807500000000000 : ℝ)*(X 1 0+X 2 0)+(144598594093/152300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (3806795645683223/3807500000000000 : ℝ)) (alpha := (144598594093/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3806795645683223/3807500000000000 : ℝ)*(X 0 1+X 2 1)+(144598594093/152300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (3806795645683223/3807500000000000 : ℝ)) (alpha := (144598594093/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3806795645683223/3807500000000000 : ℝ)*(X 0 2+X 1 2)+(144598594093/152300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (3107/20000 : ℝ)) (c := (3806795645683223/3807500000000000 : ℝ)) (alpha := (144598594093/152300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1830239087/10000000000 : ℝ)*X 0 0+(1357534789/2500000000 : ℝ)*X 0 1+(2609302191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350178489/10000000000 : ℝ)*X 1 0+(-1938528411/10000000000 : ℝ)*X 1 1+(5218603919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350178279/10000000000 : ℝ)*X 2 0+(5218604241/10000000000 : ℝ)*X 2 1+(-387705653/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((532223911/1250000000 : ℝ)*X 0 0+(401937391/1000000000 : ℝ)*X 0 1+(4507849911/10000000000 : ℝ)*X 0 2+(532223911/1250000000 : ℝ)*X 1 0+(401937391/1000000000 : ℝ)*X 1 1+(4507849911/10000000000 : ℝ)*X 1 2+(532223911/1250000000 : ℝ)*X 2 0+(401937391/1000000000 : ℝ)*X 2 1+(4507849911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-915133813/5000000000 : ℝ)*X 0 0+(1043940133/2000000000 : ℝ)*X 0 1+(1357258613/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058887993/2000000000 : ℝ)*X 1 0+(-1728098437/10000000000 : ℝ)*X 1 1+(2714517093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294440557/10000000000 : ℝ)*X 2 0+(1085806787/2000000000 : ℝ)*X 2 1+(-1728097969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257855911/10000000000 : ℝ)*X 0 0+(450531663/1000000000 : ℝ)*X 0 1+(160877051/400000000 : ℝ)*X 0 2+(4257855911/10000000000 : ℝ)*X 1 0+(450531663/1000000000 : ℝ)*X 1 1+(160877051/400000000 : ℝ)*X 1 2+(4257855911/10000000000 : ℝ)*X 2 0+(450531663/1000000000 : ℝ)*X 2 1+(160877051/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2316431486118489129876621/190375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (365295393/20000000000000 : ℝ)*(base19) + (264831787/25000000000000 : ℝ)*(base23) + (311163857/100000000000000 : ℝ)*(lower2) + (423124097/100000000000000 : ℝ)*(upper3) + (115120481/100000000000000 : ℝ)*(upper5) + (1693646111853721/50000000000000 : ℝ)*(major0) + (1693646111853721/50000000000000 : ℝ)*(major1) + (1693646111853721/50000000000000 : ℝ)*(major2) + (4727370428685021/100000000000000 : ℝ)*(sp0) + (4727379594416637/100000000000000 : ℝ)*(sp1) + (2363690180783227/50000000000000 : ℝ)*(sp2) + (2047190651588353/100000000000000 : ℝ)*(sp3) + (549610429/5000000000000 : ℝ)*(sp4) + (598467097/5000000000000 : ℝ)*(sp7) + (2047202620930293/100000000000000 : ℝ)*(f.failure) + (2363690710446801/50000000000000 : ℝ)*(f.sum) + (16309697233549/7615000000000000000000000000 : ℝ)*base66 + (958575025359071/95187500000000000000000000000 : ℝ)*base68 + (774885738624733/190375000000000000000000000000 : ℝ)*base69 + (1183307176917267/190375000000000000000000000000 : ℝ)*base72 + (28761208574039/7615000000000000000000000000 : ℝ)*base74 + (1410519571724071/95187500000000000000000000000 : ℝ)*base76 + (860532686988571/95187500000000000000000000000 : ℝ)*base78 + (12902837481357/743652343750000000000000000 : ℝ)*base80 + (43433719198711/7615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (40217857/10000000000000000000000 : ℝ)*base89 + (40217857/10000000000000000000000 : ℝ)*base91 + (40217857/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357135866206104799177137/47593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (895196541/100000000000000 : ℝ)*(base19) + (77302167/5000000000000 : ℝ)*(base23) + (116167381/100000000000000 : ℝ)*(upper3) + (1028269/5000000000000 : ℝ)*(lower4) + (353119091/100000000000000 : ℝ)*(upper5) + (106965476859797/3125000000000 : ℝ)*(major0) + (106965476859797/3125000000000 : ℝ)*(major1) + (106965476859797/3125000000000 : ℝ)*(major2) + (3943202639/50000000000000 : ℝ)*(sp1) + (15281707999/100000000000000 : ℝ)*(sp2) + (2388534990172339/50000000000000 : ℝ)*(sp4) + (4777061198742859/100000000000000 : ℝ)*(sp5) + (4777053152593339/100000000000000 : ℝ)*(sp6) + (2068720288554337/100000000000000 : ℝ)*(sp7) + (2068720288554337/100000000000000 : ℝ)*(f.failure) + (2388534990172339/50000000000000 : ℝ)*(f.sum) + (2985677992213/7615000000000000000000000000 : ℝ)*base66 + (119795091656899/47593750000000000000000000000 : ℝ)*base67 + (891377279955971/190375000000000000000000000000 : ℝ)*base69 + (389521927682149/47593750000000000000000000000 : ℝ)*base71 + (11386683747563/7615000000000000000000000000 : ℝ)*base74 + (2294323797030971/190375000000000000000000000000 : ℝ)*base75 + (661756878001529/190375000000000000000000000000 : ℝ)*base78 + (2019104137461173/95187500000000000000000000000 : ℝ)*base79 + (10777672447263/7615000000000000000000000000 : ℝ)*base82 + (62014013/10000000000000000000000 : ℝ)*base89 + (62014013/10000000000000000000000 : ℝ)*base91 + (62014013/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1538_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3107/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1538_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1538_s5_0 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-915138339/5000000000 : ℝ)*x 0 + (2714948691/5000000000 : ℝ)*x 1 + (5218821157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915138339/5000000000 : ℝ)^4573 ≤ (11213191564981/100000000000000 : ℝ)^3549 := by
    have hnat : (915138339 : ℕ)^4573*100000000000000^3549 ≤ 11213191564981^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915138339 5000000000 11213191564981 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714948691/5000000000 : ℝ)^4573 ≤ (22763578098991/50000000000000 : ℝ)^3549 := by
    have hnat : (2714948691 : ℕ)^4573*50000000000000^3549 ≤ 22763578098991^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714948691 5000000000 22763578098991 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218821157/10000000000 : ℝ)^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549 := by
    have hnat : (5218821157 : ℕ)^4573*50000000000000^3549 ≤ 21629826106839^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218821157 10000000000 21629826106839 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-915138339/5000000000 : ℝ), (2714948691/5000000000 : ℝ), (5218821157/10000000000 : ℝ)] ![(11213191564981/100000000000000 : ℝ), (22763578098991/50000000000000 : ℝ), (21629826106839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-915138339/5000000000 : ℝ)|^4573 ≤ (11213191564981/100000000000000 : ℝ)^3549
        have hw : |(-915138339/5000000000 : ℝ)|=(915138339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714948691/5000000000 : ℝ)|^4573 ≤ (22763578098991/50000000000000 : ℝ)^3549
        have hw : |(2714948691/5000000000 : ℝ)|=(2714948691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218821157/10000000000 : ℝ)|^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549
        have hw : |(5218821157/10000000000 : ℝ)|=(5218821157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_1 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350114621/10000000000 : ℝ)*x 0 + (-484581231/2500000000 : ℝ)*x 1 + (5218821157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350114621/10000000000 : ℝ)^4573 ≤ (5583379693637/12500000000000 : ℝ)^3549 := by
    have hnat : (5350114621 : ℕ)^4573*12500000000000^3549 ≤ 5583379693637^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350114621 10000000000 5583379693637 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484581231/2500000000 : ℝ)^4573 ≤ (6036655110411/50000000000000 : ℝ)^3549 := by
    have hnat : (484581231 : ℕ)^4573*50000000000000^3549 ≤ 6036655110411^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484581231 2500000000 6036655110411 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218821157/10000000000 : ℝ)^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549 := by
    have hnat : (5218821157 : ℕ)^4573*50000000000000^3549 ≤ 21629826106839^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218821157 10000000000 21629826106839 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350114621/10000000000 : ℝ), (-484581231/2500000000 : ℝ), (5218821157/10000000000 : ℝ)] ![(5583379693637/12500000000000 : ℝ), (6036655110411/50000000000000 : ℝ), (21629826106839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350114621/10000000000 : ℝ)|^4573 ≤ (5583379693637/12500000000000 : ℝ)^3549
        have hw : |(5350114621/10000000000 : ℝ)|=(5350114621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484581231/2500000000 : ℝ)|^4573 ≤ (6036655110411/50000000000000 : ℝ)^3549
        have hw : |(-484581231/2500000000 : ℝ)|=(484581231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218821157/10000000000 : ℝ)|^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549
        have hw : |(5218821157/10000000000 : ℝ)|=(5218821157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_2 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350114621/10000000000 : ℝ)*x 0 + (5218821157/10000000000 : ℝ)*x 1 + (-484581231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350114621/10000000000 : ℝ)^4573 ≤ (5583379693637/12500000000000 : ℝ)^3549 := by
    have hnat : (5350114621 : ℕ)^4573*12500000000000^3549 ≤ 5583379693637^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350114621 10000000000 5583379693637 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218821157/10000000000 : ℝ)^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549 := by
    have hnat : (5218821157 : ℕ)^4573*50000000000000^3549 ≤ 21629826106839^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218821157 10000000000 21629826106839 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484581231/2500000000 : ℝ)^4573 ≤ (6036655110411/50000000000000 : ℝ)^3549 := by
    have hnat : (484581231 : ℕ)^4573*50000000000000^3549 ≤ 6036655110411^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484581231 2500000000 6036655110411 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350114621/10000000000 : ℝ), (5218821157/10000000000 : ℝ), (-484581231/2500000000 : ℝ)] ![(5583379693637/12500000000000 : ℝ), (21629826106839/50000000000000 : ℝ), (6036655110411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350114621/10000000000 : ℝ)|^4573 ≤ (5583379693637/12500000000000 : ℝ)^3549
        have hw : |(5350114621/10000000000 : ℝ)|=(5350114621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218821157/10000000000 : ℝ)|^4573 ≤ (21629826106839/50000000000000 : ℝ)^3549
        have hw : |(5218821157/10000000000 : ℝ)|=(5218821157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484581231/2500000000 : ℝ)|^4573 ≤ (6036655110411/50000000000000 : ℝ)^3549
        have hw : |(-484581231/2500000000 : ℝ)|=(484581231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_3 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266113331/625000000 : ℝ)*x 0 + (803980403/2000000000 : ℝ)*x 1 + (450731733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266113331/625000000 : ℝ)^4573 ≤ (6656180471771/20000000000000 : ℝ)^3549 := by
    have hnat : (266113331 : ℕ)^4573*20000000000000^3549 ≤ 6656180471771^3549*625000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266113331 625000000 6656180471771 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803980403/2000000000 : ℝ)^4573 ≤ (7726076086421/25000000000000 : ℝ)^3549 := by
    have hnat : (803980403 : ℕ)^4573*25000000000000^3549 ≤ 7726076086421^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803980403 2000000000 7726076086421 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450731733/1000000000 : ℝ)^4573 ≤ (17907396642203/50000000000000 : ℝ)^3549 := by
    have hnat : (450731733 : ℕ)^4573*50000000000000^3549 ≤ 17907396642203^3549*1000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450731733 1000000000 17907396642203 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266113331/625000000 : ℝ), (803980403/2000000000 : ℝ), (450731733/1000000000 : ℝ)] ![(6656180471771/20000000000000 : ℝ), (7726076086421/25000000000000 : ℝ), (17907396642203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266113331/625000000 : ℝ)|^4573 ≤ (6656180471771/20000000000000 : ℝ)^3549
        have hw : |(266113331/625000000 : ℝ)|=(266113331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803980403/2000000000 : ℝ)|^4573 ≤ (7726076086421/25000000000000 : ℝ)^3549
        have hw : |(803980403/2000000000 : ℝ)|=(803980403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450731733/1000000000 : ℝ)|^4573 ≤ (17907396642203/50000000000000 : ℝ)^3549
        have hw : |(450731733/1000000000 : ℝ)|=(450731733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_4 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-915152317/5000000000 : ℝ)*x 0 + (2609956783/5000000000 : ℝ)*x 1 + (5428796907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915152317/5000000000 : ℝ)^4573 ≤ (5606706127753/50000000000000 : ℝ)^3549 := by
    have hnat : (915152317 : ℕ)^4573*50000000000000^3549 ≤ 5606706127753^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915152317 5000000000 5606706127753 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609956783/5000000000 : ℝ)^4573 ≤ (10817830105637/25000000000000 : ℝ)^3549 := by
    have hnat : (2609956783 : ℕ)^4573*25000000000000^3549 ≤ 10817830105637^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609956783 5000000000 10817830105637 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428796907/10000000000 : ℝ)^4573 ≤ (5689408412551/12500000000000 : ℝ)^3549 := by
    have hnat : (5428796907 : ℕ)^4573*12500000000000^3549 ≤ 5689408412551^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428796907 10000000000 5689408412551 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-915152317/5000000000 : ℝ), (2609956783/5000000000 : ℝ), (5428796907/10000000000 : ℝ)] ![(5606706127753/50000000000000 : ℝ), (10817830105637/25000000000000 : ℝ), (5689408412551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-915152317/5000000000 : ℝ)|^4573 ≤ (5606706127753/50000000000000 : ℝ)^3549
        have hw : |(-915152317/5000000000 : ℝ)|=(915152317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609956783/5000000000 : ℝ)|^4573 ≤ (10817830105637/25000000000000 : ℝ)^3549
        have hw : |(2609956783/5000000000 : ℝ)|=(2609956783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428796907/10000000000 : ℝ)|^4573 ≤ (5689408412551/12500000000000 : ℝ)^3549
        have hw : |(5428796907/10000000000 : ℝ)|=(5428796907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_5 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294497473/10000000000 : ℝ)*x 0 + (-1728349197/10000000000 : ℝ)*x 1 + (84824951/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294497473/10000000000 : ℝ)^4573 ≤ (44069624703361/100000000000000 : ℝ)^3549 := by
    have hnat : (5294497473 : ℕ)^4573*100000000000000^3549 ≤ 44069624703361^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294497473 10000000000 44069624703361 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1728349197/10000000000 : ℝ)^4573 ≤ (1041510845007/10000000000000 : ℝ)^3549 := by
    have hnat : (1728349197 : ℕ)^4573*10000000000000^3549 ≤ 1041510845007^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728349197 10000000000 1041510845007 10000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84824951/156250000 : ℝ)^4573 ≤ (364122134687/800000000000 : ℝ)^3549 := by
    have hnat : (84824951 : ℕ)^4573*800000000000^3549 ≤ 364122134687^3549*156250000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84824951 156250000 364122134687 800000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294497473/10000000000 : ℝ), (-1728349197/10000000000 : ℝ), (84824951/156250000 : ℝ)] ![(44069624703361/100000000000000 : ℝ), (1041510845007/10000000000000 : ℝ), (364122134687/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294497473/10000000000 : ℝ)|^4573 ≤ (44069624703361/100000000000000 : ℝ)^3549
        have hw : |(5294497473/10000000000 : ℝ)|=(5294497473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1728349197/10000000000 : ℝ)|^4573 ≤ (1041510845007/10000000000000 : ℝ)^3549
        have hw : |(-1728349197/10000000000 : ℝ)|=(1728349197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84824951/156250000 : ℝ)|^4573 ≤ (364122134687/800000000000 : ℝ)^3549
        have hw : |(84824951/156250000 : ℝ)|=(84824951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_6 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647248709/5000000000 : ℝ)*x 0 + (5428796903/10000000000 : ℝ)*x 1 + (-864174609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647248709/5000000000 : ℝ)^4573 ≤ (44069624113469/100000000000000 : ℝ)^3549 := by
    have hnat : (2647248709 : ℕ)^4573*100000000000000^3549 ≤ 44069624113469^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647248709 5000000000 44069624113469 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428796903/10000000000 : ℝ)^4573 ≤ (11378816814299/25000000000000 : ℝ)^3549 := by
    have hnat : (5428796903 : ℕ)^4573*25000000000000^3549 ≤ 11378816814299^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428796903 10000000000 11378816814299 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864174609/5000000000 : ℝ)^4573 ≤ (1041510861313/10000000000000 : ℝ)^3549 := by
    have hnat : (864174609 : ℕ)^4573*10000000000000^3549 ≤ 1041510861313^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864174609 5000000000 1041510861313 10000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647248709/5000000000 : ℝ), (5428796903/10000000000 : ℝ), (-864174609/5000000000 : ℝ)] ![(44069624113469/100000000000000 : ℝ), (11378816814299/25000000000000 : ℝ), (1041510861313/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647248709/5000000000 : ℝ)|^4573 ≤ (44069624113469/100000000000000 : ℝ)^3549
        have hw : |(2647248709/5000000000 : ℝ)|=(2647248709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428796903/10000000000 : ℝ)|^4573 ≤ (11378816814299/25000000000000 : ℝ)^3549
        have hw : |(5428796903/10000000000 : ℝ)|=(5428796903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864174609/5000000000 : ℝ)|^4573 ≤ (1041510861313/10000000000000 : ℝ)^3549
        have hw : |(-864174609/5000000000 : ℝ)|=(864174609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s5_7 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257877827/10000000000 : ℝ)*x 0 + (1126198673/2500000000 : ℝ)*x 1 + (4022443291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257877827/10000000000 : ℝ)^4573 ≤ (65003031833/195312500000 : ℝ)^3549 := by
    have hnat : (4257877827 : ℕ)^4573*195312500000^3549 ≤ 65003031833^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257877827 10000000000 65003031833 195312500000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126198673/2500000000 : ℝ)^4573 ≤ (35788967151749/100000000000000 : ℝ)^3549 := by
    have hnat : (1126198673 : ℕ)^4573*100000000000000^3549 ≤ 35788967151749^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126198673 2500000000 35788967151749 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022443291/10000000000 : ℝ)^4573 ≤ (3866185067937/12500000000000 : ℝ)^3549 := by
    have hnat : (4022443291 : ℕ)^4573*12500000000000^3549 ≤ 3866185067937^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022443291 10000000000 3866185067937 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257877827/10000000000 : ℝ), (1126198673/2500000000 : ℝ), (4022443291/10000000000 : ℝ)] ![(65003031833/195312500000 : ℝ), (35788967151749/100000000000000 : ℝ), (3866185067937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257877827/10000000000 : ℝ)|^4573 ≤ (65003031833/195312500000 : ℝ)^3549
        have hw : |(4257877827/10000000000 : ℝ)|=(4257877827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126198673/2500000000 : ℝ)|^4573 ≤ (35788967151749/100000000000000 : ℝ)^3549
        have hw : |(1126198673/2500000000 : ℝ)|=(1126198673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022443291/10000000000 : ℝ)|^4573 ≤ (3866185067937/12500000000000 : ℝ)^3549
        have hw : |(4022443291/10000000000 : ℝ)|=(4022443291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1538_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2753/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11007/100000 : ℝ) ^ (4571/1024 : ℝ) ≤ (82405760307069/1562500000000000000 : ℝ) := by
    have hpowers : (11007/100000 : ℝ)^4571 ≤ (82405760307069/1562500000000000000 : ℝ)^1024 := by
      have hnat : (11007 : ℕ)^4571*1562500000000000000^1024 ≤ 82405760307069^1024*100000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11007 100000 82405760307069 1562500000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11007/100000 : ℝ)) (X := (82405760307069/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4571/1024 : ℝ) ≤ (2423801780538531/10000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4571 ≤ (2423801780538531/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4571*10000000000000000000^1024 ≤ 2423801780538531^1024*10000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 2423801780538531 10000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (2423801780538531/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781332405760307069/781250000000000000 : ℝ) ≤ (2500059071569729/2500000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (781332405760307069/781250000000000000 : ℝ)^1024 ≤ (2500059071569729/2500000000000000 : ℝ)^4571 := by
      have hnat : (781332405760307069 : ℕ)^1024*2500000000000000^4571 ≤ 2500059071569729^4571*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781332405760307069 781250000000000000 2500059071569729 2500000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500059071569729/2500000000000000 : ℝ)) (X := (781332405760307069/781250000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014755993232518863/50000000000000000000 : ℝ) ≤ (1000066105478933/1000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50014755993232518863/50000000000000000000 : ℝ)^1024 ≤ (1000066105478933/1000000000000000 : ℝ)^4571 := by
      have hnat : (50014755993232518863 : ℕ)^1024*1000000000000000^4571 ≤ 1000066105478933^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014755993232518863 50000000000000000000 1000066105478933 1000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066105478933/1000000000000000 : ℝ)) (X := (50014755993232518863/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002423801780538531/5000000000000000000 : ℝ) ≤ (312533931978117/312500000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (5002423801780538531/5000000000000000000 : ℝ)^1024 ≤ (312533931978117/312500000000000 : ℝ)^4571 := by
      have hnat : (5002423801780538531 : ℕ)^1024*312500000000000^4571 ≤ 312533931978117^4571*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002423801780538531 5000000000000000000 312533931978117 312500000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312533931978117/312500000000000 : ℝ)) (X := (5002423801780538531/5000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(82405760307069/1562500000000000000 : ℝ) ≤ ((5602713552175015829/5603750000000000000 : ℝ)+2*(212384255207/224150000000000 : ℝ)*(11007/100000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (5602713552175015829/5603750000000000000 : ℝ)+2*(212384255207/224150000000000 : ℝ)*(11007/100000 : ℝ)=(2500059071569729/2500000000000000 : ℝ) by norm_num, show 1+2*(82405760307069/1562500000000000000 : ℝ)=(781332405760307069/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2423801780538531/10000000000000000000 : ℝ)+(82405760307069/1562500000000000000 : ℝ) ≤ ((5602713552175015829/5603750000000000000 : ℝ)+(212384255207/224150000000000 : ℝ)*((1549/10000 : ℝ)+(11007/100000 : ℝ)))^(4571/1024 : ℝ) := by
    rw [show (5602713552175015829/5603750000000000000 : ℝ)+(212384255207/224150000000000 : ℝ)*((1549/10000 : ℝ)+(11007/100000 : ℝ))=(1000066105478933/1000000000000000 : ℝ) by norm_num, show 1+(2423801780538531/10000000000000000000 : ℝ)+(82405760307069/1562500000000000000 : ℝ)=(50014755993232518863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2423801780538531/10000000000000000000 : ℝ) ≤ ((5602713552175015829/5603750000000000000 : ℝ)+2*(212384255207/224150000000000 : ℝ)*(1549/10000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (5602713552175015829/5603750000000000000 : ℝ)+2*(212384255207/224150000000000 : ℝ)*(1549/10000 : ℝ)=(312533931978117/312500000000000 : ℝ) by norm_num, show 1+2*(2423801780538531/10000000000000000000 : ℝ)=(5002423801780538531/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5602713552175015829/5603750000000000000 : ℝ)*(X 1 0+X 2 0)+(212384255207/224150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5602713552175015829/5603750000000000000 : ℝ)) (alpha := (212384255207/224150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5602713552175015829/5603750000000000000 : ℝ)*(X 0 1+X 2 1)+(212384255207/224150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5602713552175015829/5603750000000000000 : ℝ)) (alpha := (212384255207/224150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5602713552175015829/5603750000000000000 : ℝ)*(X 0 2+X 1 2)+(212384255207/224150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5602713552175015829/5603750000000000000 : ℝ)) (alpha := (212384255207/224150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-915138339/5000000000 : ℝ)*X 0 0+(2714948691/5000000000 : ℝ)*X 0 1+(5218821157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350114621/10000000000 : ℝ)*X 1 0+(-484581231/2500000000 : ℝ)*X 1 1+(5218821157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350114621/10000000000 : ℝ)*X 2 0+(5218821157/10000000000 : ℝ)*X 2 1+(-484581231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((266113331/625000000 : ℝ)*X 0 0+(803980403/2000000000 : ℝ)*X 0 1+(450731733/1000000000 : ℝ)*X 0 2+(266113331/625000000 : ℝ)*X 1 0+(803980403/2000000000 : ℝ)*X 1 1+(450731733/1000000000 : ℝ)*X 1 2+(266113331/625000000 : ℝ)*X 2 0+(803980403/2000000000 : ℝ)*X 2 1+(450731733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-915152317/5000000000 : ℝ)*X 0 0+(2609956783/5000000000 : ℝ)*X 0 1+(5428796907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294497473/10000000000 : ℝ)*X 1 0+(-1728349197/10000000000 : ℝ)*X 1 1+(84824951/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647248709/5000000000 : ℝ)*X 2 0+(5428796903/10000000000 : ℝ)*X 2 1+(-864174609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257877827/10000000000 : ℝ)*X 0 0+(1126198673/2500000000 : ℝ)*X 0 1+(4022443291/10000000000 : ℝ)*X 0 2+(4257877827/10000000000 : ℝ)*X 1 0+(1126198673/2500000000 : ℝ)*X 1 1+(4022443291/10000000000 : ℝ)*X 1 2+(4257877827/10000000000 : ℝ)*X 2 0+(1126198673/2500000000 : ℝ)*X 2 1+(4022443291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102789800563967594654887689/14009375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316695457/25000000000000 : ℝ)*(base19) + (295657763/25000000000000 : ℝ)*(base23) + (4502163/10000000000000 : ℝ)*(lower2) + (182182967/100000000000000 : ℝ)*(upper3) + (60568697/50000000000000 : ℝ)*(upper5) + (339466135677197/10000000000000 : ℝ)*(major0) + (339466135677197/10000000000000 : ℝ)*(major1) + (3394661356771971/100000000000000 : ℝ)*(major2) + (1184411485666437/25000000000000 : ℝ)*(sp0) + (4737664844311951/100000000000000 : ℝ)*(sp1) + (2368832464231363/50000000000000 : ℝ)*(sp2) + (1025823447238217/50000000000000 : ℝ)*(sp3) + (2016842803/10000000000000 : ℝ)*(sp4) + (4731699939/50000000000000 : ℝ)*(sp7) + (2051656357876311/100000000000000 : ℝ)*(f.failure) + (2368833055546889/50000000000000 : ℝ)*(f.sum) + (57735812374703/22415000000000000000000000000 : ℝ)*base66 + (234421526375231187/56037500000000000000000000000000 : ℝ)*base68 + (452734478111778959/560375000000000000000000000000000 : ℝ)*base69 + (779908390296943687/56037500000000000000000000000000 : ℝ)*base72 + (128204984988443/22415000000000000000000000000 : ℝ)*base74 + (4046524052171096041/560375000000000000000000000000000 : ℝ)*base76 + (315102901632773687/56037500000000000000000000000000 : ℝ)*base78 + (239254332681723687/56037500000000000000000000000000 : ℝ)*base80 + (10387835818343/2241500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15843739/10000000000000000000000 : ℝ)*base89 + (15843739/10000000000000000000000 : ℝ)*base91 + (84156261/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (282356680413015674635747629/35023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (163363867/12500000000000 : ℝ)*(base19) + (1342825687/100000000000000 : ℝ)*(base23) + (422360221/100000000000000 : ℝ)*(lower1) + (154469763/100000000000000 : ℝ)*(upper3) + (22156083/50000000000000 : ℝ)*(lower4) + (88217323/50000000000000 : ℝ)*(upper5) + (857563597101759/25000000000000 : ℝ)*(major0) + (857563597101759/25000000000000 : ℝ)*(major1) + (857563597101759/25000000000000 : ℝ)*(major2) + (92890769/50000000000000 : ℝ)*(sp2) + (598417566109581/12500000000000 : ℝ)*(sp4) + (299208701372857/6250000000000 : ℝ)*(sp5) + (4787339000269423/100000000000000 : ℝ)*(sp6) + (2073167979206227/100000000000000 : ℝ)*(sp7) + (2073167979206227/100000000000000 : ℝ)*(f.failure) + (598417566109581/12500000000000 : ℝ)*(f.sum) + (17053255751649/22415000000000000000000000000 : ℝ)*base65 + (5739388446627056789/140093750000000000000000000000000 : ℝ)*base68 + (990062794642775539/140093750000000000000000000000000 : ℝ)*base70 + (12469545985016724461/140093750000000000000000000000000 : ℝ)*base71 + (14292786475599/5603750000000000000000000000 : ℝ)*base74 + (14928201703680474461/140093750000000000000000000000000 : ℝ)*base75 + (960803493192275539/140093750000000000000000000000000 : ℝ)*base78 + (304674117788338039/140093750000000000000000000000000 : ℝ)*base80 + (30705854917539/22415000000000000000000000000 : ℝ)*base81 + (97411623/10000000000000000000000 : ℝ)*base89 + (97411623/10000000000000000000000 : ℝ)*base91 + (97411623/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1538_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1538_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1538_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1538_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1538_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1538_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1538_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
