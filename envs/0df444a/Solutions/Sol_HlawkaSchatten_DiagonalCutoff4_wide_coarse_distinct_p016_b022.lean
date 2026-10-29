-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b022
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:36.262883+00:00
-- url     : https://prove2.me/submissions/aa014207-45e6-4831-b581-96e64e2e3e75

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c316046_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-200903101/2000000000 : ℝ)*x 0 + (-5508122927/10000000000 : ℝ)*x 1 + (-5508122927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200903101/2000000000 : ℝ)^39 ≤ (1110266061837/20000000000000 : ℝ)^31 := by
    have hnat : (200903101 : ℕ)^39*20000000000000^31 ≤ 1110266061837^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200903101 2000000000 1110266061837 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508122927/10000000000 : ℝ)^39 ≤ (11806083710549/25000000000000 : ℝ)^31 := by
    have hnat : (5508122927 : ℕ)^39*25000000000000^31 ≤ 11806083710549^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508122927 10000000000 11806083710549 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508122927/10000000000 : ℝ)^39 ≤ (11806083710549/25000000000000 : ℝ)^31 := by
    have hnat : (5508122927 : ℕ)^39*25000000000000^31 ≤ 11806083710549^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508122927 10000000000 11806083710549 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200903101/2000000000 : ℝ), (-5508122927/10000000000 : ℝ), (-5508122927/10000000000 : ℝ)] ![(1110266061837/20000000000000 : ℝ), (11806083710549/25000000000000 : ℝ), (11806083710549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200903101/2000000000 : ℝ)|^39 ≤ (1110266061837/20000000000000 : ℝ)^31
        have hw : |(-200903101/2000000000 : ℝ)|=(200903101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5508122927/10000000000 : ℝ)|^39 ≤ (11806083710549/25000000000000 : ℝ)^31
        have hw : |(-5508122927/10000000000 : ℝ)|=(5508122927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5508122927/10000000000 : ℝ)|^39 ≤ (11806083710549/25000000000000 : ℝ)^31
        have hw : |(-5508122927/10000000000 : ℝ)|=(5508122927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1210361009/2500000000 : ℝ)*x 0 + (958204711/2500000000 : ℝ)*x 1 + (-958204711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1210361009/2500000000 : ℝ)^39 ≤ (40149313164899/100000000000000 : ℝ)^31 := by
    have hnat : (1210361009 : ℕ)^39*100000000000000^31 ≤ 40149313164899^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210361009 2500000000 40149313164899 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958204711/2500000000 : ℝ)^39 ≤ (29925343410079/100000000000000 : ℝ)^31 := by
    have hnat : (958204711 : ℕ)^39*100000000000000^31 ≤ 29925343410079^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958204711 2500000000 29925343410079 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958204711/2500000000 : ℝ)^39 ≤ (29925343410079/100000000000000 : ℝ)^31 := by
    have hnat : (958204711 : ℕ)^39*100000000000000^31 ≤ 29925343410079^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958204711 2500000000 29925343410079 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1210361009/2500000000 : ℝ), (958204711/2500000000 : ℝ), (-958204711/2500000000 : ℝ)] ![(40149313164899/100000000000000 : ℝ), (29925343410079/100000000000000 : ℝ), (29925343410079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1210361009/2500000000 : ℝ)|^39 ≤ (40149313164899/100000000000000 : ℝ)^31
        have hw : |(1210361009/2500000000 : ℝ)|=(1210361009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958204711/2500000000 : ℝ)|^39 ≤ (29925343410079/100000000000000 : ℝ)^31
        have hw : |(958204711/2500000000 : ℝ)|=(958204711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-958204711/2500000000 : ℝ)|^39 ≤ (29925343410079/100000000000000 : ℝ)^31
        have hw : |(-958204711/2500000000 : ℝ)|=(958204711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1627413677/2000000000 : ℝ)*x 0 + (-1782559423/10000000000 : ℝ)*x 1 + (-1782559423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1627413677/2000000000 : ℝ)^39 ≤ (4822174722317/6250000000000 : ℝ)^31 := by
    have hnat : (1627413677 : ℕ)^39*6250000000000^31 ≤ 4822174722317^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627413677 2000000000 4822174722317 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782559423/10000000000 : ℝ)^39 ≤ (1142260220847/10000000000000 : ℝ)^31 := by
    have hnat : (1782559423 : ℕ)^39*10000000000000^31 ≤ 1142260220847^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782559423 10000000000 1142260220847 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1782559423/10000000000 : ℝ)^39 ≤ (1142260220847/10000000000000 : ℝ)^31 := by
    have hnat : (1782559423 : ℕ)^39*10000000000000^31 ≤ 1142260220847^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782559423 10000000000 1142260220847 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1627413677/2000000000 : ℝ), (-1782559423/10000000000 : ℝ), (-1782559423/10000000000 : ℝ)] ![(4822174722317/6250000000000 : ℝ), (1142260220847/10000000000000 : ℝ), (1142260220847/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1627413677/2000000000 : ℝ)|^39 ≤ (4822174722317/6250000000000 : ℝ)^31
        have hw : |(1627413677/2000000000 : ℝ)|=(1627413677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782559423/10000000000 : ℝ)|^39 ≤ (1142260220847/10000000000000 : ℝ)^31
        have hw : |(-1782559423/10000000000 : ℝ)|=(1782559423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1782559423/10000000000 : ℝ)|^39 ≤ (1142260220847/10000000000000 : ℝ)^31
        have hw : |(-1782559423/10000000000 : ℝ)|=(1782559423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-523251787/5000000000 : ℝ)*x 0 + (-2841721971/5000000000 : ℝ)*x 1 + (-2651946001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523251787/5000000000 : ℝ)^39 ≤ (5844812424099/100000000000000 : ℝ)^31 := by
    have hnat : (523251787 : ℕ)^39*100000000000000^31 ≤ 5844812424099^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523251787 5000000000 5844812424099 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841721971/5000000000 : ℝ)^39 ≤ (9824614822699/20000000000000 : ℝ)^31 := by
    have hnat : (2841721971 : ℕ)^39*20000000000000^31 ≤ 9824614822699^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841721971 5000000000 9824614822699 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2651946001/5000000000 : ℝ)^39 ≤ (45032113447783/100000000000000 : ℝ)^31 := by
    have hnat : (2651946001 : ℕ)^39*100000000000000^31 ≤ 45032113447783^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651946001 5000000000 45032113447783 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523251787/5000000000 : ℝ), (-2841721971/5000000000 : ℝ), (-2651946001/5000000000 : ℝ)] ![(5844812424099/100000000000000 : ℝ), (9824614822699/20000000000000 : ℝ), (45032113447783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523251787/5000000000 : ℝ)|^39 ≤ (5844812424099/100000000000000 : ℝ)^31
        have hw : |(-523251787/5000000000 : ℝ)|=(523251787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2841721971/5000000000 : ℝ)|^39 ≤ (9824614822699/20000000000000 : ℝ)^31
        have hw : |(-2841721971/5000000000 : ℝ)|=(2841721971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2651946001/5000000000 : ℝ)|^39 ≤ (45032113447783/100000000000000 : ℝ)^31
        have hw : |(-2651946001/5000000000 : ℝ)|=(2651946001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4738448589/10000000000 : ℝ)*x 0 + (263183437/625000000 : ℝ)*x 1 + (-222279867/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4738448589/10000000000 : ℝ)^39 ≤ (19538867296227/50000000000000 : ℝ)^31 := by
    have hnat : (4738448589 : ℕ)^39*50000000000000^31 ≤ 19538867296227^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738448589 10000000000 19538867296227 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263183437/625000000 : ℝ)^39 ≤ (16842787529231/50000000000000 : ℝ)^31 := by
    have hnat : (263183437 : ℕ)^39*50000000000000^31 ≤ 16842787529231^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263183437 625000000 16842787529231 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222279867/625000000 : ℝ)^39 ≤ (13618345164571/50000000000000 : ℝ)^31 := by
    have hnat : (222279867 : ℕ)^39*50000000000000^31 ≤ 13618345164571^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222279867 625000000 13618345164571 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4738448589/10000000000 : ℝ), (263183437/625000000 : ℝ), (-222279867/625000000 : ℝ)] ![(19538867296227/50000000000000 : ℝ), (16842787529231/50000000000000 : ℝ), (13618345164571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4738448589/10000000000 : ℝ)|^39 ≤ (19538867296227/50000000000000 : ℝ)^31
        have hw : |(4738448589/10000000000 : ℝ)|=(4738448589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263183437/625000000 : ℝ)|^39 ≤ (16842787529231/50000000000000 : ℝ)^31
        have hw : |(263183437/625000000 : ℝ)|=(263183437/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222279867/625000000 : ℝ)|^39 ≤ (13618345164571/50000000000000 : ℝ)^31
        have hw : |(-222279867/625000000 : ℝ)|=(222279867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4738449751/10000000000 : ℝ)*x 0 + (-3471708733/10000000000 : ℝ)*x 1 + (4291637461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4738449751/10000000000 : ℝ)^39 ≤ (19538873324213/50000000000000 : ℝ)^31 := by
    have hnat : (4738449751 : ℕ)^39*50000000000000^31 ≤ 19538873324213^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738449751 10000000000 19538873324213 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3471708733/10000000000 : ℝ)^39 ≤ (13211246948403/50000000000000 : ℝ)^31 := by
    have hnat : (3471708733 : ℕ)^39*50000000000000^31 ≤ 13211246948403^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3471708733 10000000000 13211246948403 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291637461/10000000000 : ℝ)^39 ≤ (34499759443733/100000000000000 : ℝ)^31 := by
    have hnat : (4291637461 : ℕ)^39*100000000000000^31 ≤ 34499759443733^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291637461 10000000000 34499759443733 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4738449751/10000000000 : ℝ), (-3471708733/10000000000 : ℝ), (4291637461/10000000000 : ℝ)] ![(19538873324213/50000000000000 : ℝ), (13211246948403/50000000000000 : ℝ), (34499759443733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4738449751/10000000000 : ℝ)|^39 ≤ (19538873324213/50000000000000 : ℝ)^31
        have hw : |(4738449751/10000000000 : ℝ)|=(4738449751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3471708733/10000000000 : ℝ)|^39 ≤ (13211246948403/50000000000000 : ℝ)^31
        have hw : |(-3471708733/10000000000 : ℝ)|=(3471708733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291637461/10000000000 : ℝ)|^39 ≤ (34499759443733/100000000000000 : ℝ)^31
        have hw : |(4291637461/10000000000 : ℝ)|=(4291637461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4116637249/5000000000 : ℝ)*x 0 + (-57313549/400000000 : ℝ)*x 1 + (-1977698289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116637249/5000000000 : ℝ)^39 ≤ (15660833535761/20000000000000 : ℝ)^31 := by
    have hnat : (4116637249 : ℕ)^39*20000000000000^31 ≤ 15660833535761^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116637249 5000000000 15660833535761 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57313549/400000000 : ℝ)^39 ≤ (8678442249767/100000000000000 : ℝ)^31 := by
    have hnat : (57313549 : ℕ)^39*100000000000000^31 ≤ 8678442249767^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57313549 400000000 8678442249767 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977698289/10000000000 : ℝ)^39 ≤ (13017390061767/100000000000000 : ℝ)^31 := by
    have hnat : (1977698289 : ℕ)^39*100000000000000^31 ≤ 13017390061767^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977698289 10000000000 13017390061767 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116637249/5000000000 : ℝ), (-57313549/400000000 : ℝ), (-1977698289/10000000000 : ℝ)] ![(15660833535761/20000000000000 : ℝ), (8678442249767/100000000000000 : ℝ), (13017390061767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116637249/5000000000 : ℝ)|^39 ≤ (15660833535761/20000000000000 : ℝ)^31
        have hw : |(4116637249/5000000000 : ℝ)|=(4116637249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57313549/400000000 : ℝ)|^39 ≤ (8678442249767/100000000000000 : ℝ)^31
        have hw : |(-57313549/400000000 : ℝ)|=(57313549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977698289/10000000000 : ℝ)|^39 ≤ (13017390061767/100000000000000 : ℝ)^31
        have hw : |(-1977698289/10000000000 : ℝ)|=(1977698289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-182125717/5000000000 : ℝ)*x 0 + (-276141591/500000000 : ℝ)*x 1 + (-5861558399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182125717/5000000000 : ℝ)^39 ≤ (309870320079/20000000000000 : ℝ)^31 := by
    have hnat : (182125717 : ℕ)^39*20000000000000^31 ≤ 309870320079^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182125717 5000000000 309870320079 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276141591/500000000 : ℝ)^39 ≤ (23691520658809/50000000000000 : ℝ)^31 := by
    have hnat : (276141591 : ℕ)^39*50000000000000^31 ≤ 23691520658809^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276141591 500000000 23691520658809 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5861558399/10000000000 : ℝ)^39 ≤ (6383450884451/12500000000000 : ℝ)^31 := by
    have hnat : (5861558399 : ℕ)^39*12500000000000^31 ≤ 6383450884451^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861558399 10000000000 6383450884451 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182125717/5000000000 : ℝ), (-276141591/500000000 : ℝ), (-5861558399/10000000000 : ℝ)] ![(309870320079/20000000000000 : ℝ), (23691520658809/50000000000000 : ℝ), (6383450884451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182125717/5000000000 : ℝ)|^39 ≤ (309870320079/20000000000000 : ℝ)^31
        have hw : |(-182125717/5000000000 : ℝ)|=(182125717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276141591/500000000 : ℝ)|^39 ≤ (23691520658809/50000000000000 : ℝ)^31
        have hw : |(-276141591/500000000 : ℝ)|=(276141591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5861558399/10000000000 : ℝ)|^39 ≤ (6383450884451/12500000000000 : ℝ)^31
        have hw : |(-5861558399/10000000000 : ℝ)|=(5861558399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4457065173/10000000000 : ℝ)*x 0 + (787229693/2000000000 : ℝ)*x 1 + (-4130207327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4457065173/10000000000 : ℝ)^39 ≤ (36181034532117/100000000000000 : ℝ)^31 := by
    have hnat : (4457065173 : ℕ)^39*100000000000000^31 ≤ 36181034532117^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457065173 10000000000 36181034532117 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (787229693/2000000000 : ℝ)^39 ≤ (30943810017417/100000000000000 : ℝ)^31 := by
    have hnat : (787229693 : ℕ)^39*100000000000000^31 ≤ 30943810017417^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787229693 2000000000 30943810017417 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130207327/10000000000 : ℝ)^39 ≤ (32875155430903/100000000000000 : ℝ)^31 := by
    have hnat : (4130207327 : ℕ)^39*100000000000000^31 ≤ 32875155430903^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130207327 10000000000 32875155430903 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4457065173/10000000000 : ℝ), (787229693/2000000000 : ℝ), (-4130207327/10000000000 : ℝ)] ![(36181034532117/100000000000000 : ℝ), (30943810017417/100000000000000 : ℝ), (32875155430903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4457065173/10000000000 : ℝ)|^39 ≤ (36181034532117/100000000000000 : ℝ)^31
        have hw : |(4457065173/10000000000 : ℝ)|=(4457065173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(787229693/2000000000 : ℝ)|^39 ≤ (30943810017417/100000000000000 : ℝ)^31
        have hw : |(787229693/2000000000 : ℝ)|=(787229693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4130207327/10000000000 : ℝ)|^39 ≤ (32875155430903/100000000000000 : ℝ)^31
        have hw : |(-4130207327/10000000000 : ℝ)|=(4130207327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (550607929/1000000000 : ℝ)*x 0 + (-3385524349/10000000000 : ℝ)*x 1 + (3552436499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550607929/1000000000 : ℝ)^39 ≤ (23601146494591/50000000000000 : ℝ)^31 := by
    have hnat : (550607929 : ℕ)^39*50000000000000^31 ≤ 23601146494591^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550607929 1000000000 23601146494591 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3385524349/10000000000 : ℝ)^39 ≤ (3199993534683/12500000000000 : ℝ)^31 := by
    have hnat : (3385524349 : ℕ)^39*12500000000000^31 ≤ 3199993534683^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385524349 10000000000 3199993534683 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3552436499/10000000000 : ℝ)^39 ≤ (6799439679651/25000000000000 : ℝ)^31 := by
    have hnat : (3552436499 : ℕ)^39*25000000000000^31 ≤ 6799439679651^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552436499 10000000000 6799439679651 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550607929/1000000000 : ℝ), (-3385524349/10000000000 : ℝ), (3552436499/10000000000 : ℝ)] ![(23601146494591/50000000000000 : ℝ), (3199993534683/12500000000000 : ℝ), (6799439679651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550607929/1000000000 : ℝ)|^39 ≤ (23601146494591/50000000000000 : ℝ)^31
        have hw : |(550607929/1000000000 : ℝ)|=(550607929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3385524349/10000000000 : ℝ)|^39 ≤ (3199993534683/12500000000000 : ℝ)^31
        have hw : |(-3385524349/10000000000 : ℝ)|=(3385524349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3552436499/10000000000 : ℝ)|^39 ≤ (6799439679651/25000000000000 : ℝ)^31
        have hw : |(3552436499/10000000000 : ℝ)|=(3552436499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9166730123/10000000000 : ℝ)*x 0 + (-46144951/500000000 : ℝ)*x 1 + (-489751153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9166730123/10000000000 : ℝ)^39 ≤ (89632051086053/100000000000000 : ℝ)^31 := by
    have hnat : (9166730123 : ℕ)^39*100000000000000^31 ≤ 89632051086053^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9166730123 10000000000 89632051086053 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46144951/500000000 : ℝ)^39 ≤ (4989961562263/100000000000000 : ℝ)^31 := by
    have hnat : (46144951 : ℕ)^39*100000000000000^31 ≤ 4989961562263^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46144951 500000000 4989961562263 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489751153/5000000000 : ℝ)^39 ≤ (2688993671267/50000000000000 : ℝ)^31 := by
    have hnat : (489751153 : ℕ)^39*50000000000000^31 ≤ 2688993671267^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489751153 5000000000 2688993671267 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9166730123/10000000000 : ℝ), (-46144951/500000000 : ℝ), (-489751153/5000000000 : ℝ)] ![(89632051086053/100000000000000 : ℝ), (4989961562263/100000000000000 : ℝ), (2688993671267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9166730123/10000000000 : ℝ)|^39 ≤ (89632051086053/100000000000000 : ℝ)^31
        have hw : |(9166730123/10000000000 : ℝ)|=(9166730123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46144951/500000000 : ℝ)|^39 ≤ (4989961562263/100000000000000 : ℝ)^31
        have hw : |(-46144951/500000000 : ℝ)|=(46144951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489751153/5000000000 : ℝ)|^39 ≤ (2688993671267/50000000000000 : ℝ)^31
        have hw : |(-489751153/5000000000 : ℝ)|=(489751153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-364250533/10000000000 : ℝ)*x 0 + (-146539003/250000000 : ℝ)*x 1 + (-2761415259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364250533/10000000000 : ℝ)^39 ≤ (19366834737/1250000000000 : ℝ)^31 := by
    have hnat : (364250533 : ℕ)^39*1250000000000^31 ≤ 19366834737^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364250533 10000000000 19366834737 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146539003/250000000 : ℝ)^39 ≤ (10213525187769/20000000000000 : ℝ)^31 := by
    have hnat : (146539003 : ℕ)^39*20000000000000^31 ≤ 10213525187769^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146539003 250000000 10213525187769 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761415259/5000000000 : ℝ)^39 ≤ (1895321090577/4000000000000 : ℝ)^31 := by
    have hnat : (2761415259 : ℕ)^39*4000000000000^31 ≤ 1895321090577^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761415259 5000000000 1895321090577 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364250533/10000000000 : ℝ), (-146539003/250000000 : ℝ), (-2761415259/5000000000 : ℝ)] ![(19366834737/1250000000000 : ℝ), (10213525187769/20000000000000 : ℝ), (1895321090577/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364250533/10000000000 : ℝ)|^39 ≤ (19366834737/1250000000000 : ℝ)^31
        have hw : |(-364250533/10000000000 : ℝ)|=(364250533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146539003/250000000 : ℝ)|^39 ≤ (10213525187769/20000000000000 : ℝ)^31
        have hw : |(-146539003/250000000 : ℝ)|=(146539003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2761415259/5000000000 : ℝ)|^39 ≤ (1895321090577/4000000000000 : ℝ)^31
        have hw : |(-2761415259/5000000000 : ℝ)|=(2761415259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1101215479/2000000000 : ℝ)*x 0 + (3552438007/10000000000 : ℝ)*x 1 + (-3385524971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101215479/2000000000 : ℝ)^39 ≤ (5900284068931/12500000000000 : ℝ)^31 := by
    have hnat : (1101215479 : ℕ)^39*12500000000000^31 ≤ 5900284068931^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101215479 2000000000 5900284068931 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3552438007/10000000000 : ℝ)^39 ≤ (5439554648687/20000000000000 : ℝ)^31 := by
    have hnat : (3552438007 : ℕ)^39*20000000000000^31 ≤ 5439554648687^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552438007 10000000000 5439554648687 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3385524971/10000000000 : ℝ)^39 ≤ (25599954194531/100000000000000 : ℝ)^31 := by
    have hnat : (3385524971 : ℕ)^39*100000000000000^31 ≤ 25599954194531^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385524971 10000000000 25599954194531 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101215479/2000000000 : ℝ), (3552438007/10000000000 : ℝ), (-3385524971/10000000000 : ℝ)] ![(5900284068931/12500000000000 : ℝ), (5439554648687/20000000000000 : ℝ), (25599954194531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101215479/2000000000 : ℝ)|^39 ≤ (5900284068931/12500000000000 : ℝ)^31
        have hw : |(1101215479/2000000000 : ℝ)|=(1101215479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3552438007/10000000000 : ℝ)|^39 ≤ (5439554648687/20000000000000 : ℝ)^31
        have hw : |(3552438007/10000000000 : ℝ)|=(3552438007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3385524971/10000000000 : ℝ)|^39 ≤ (25599954194531/100000000000000 : ℝ)^31
        have hw : |(-3385524971/10000000000 : ℝ)|=(3385524971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4457067653/10000000000 : ℝ)*x 0 + (-2065103253/5000000000 : ℝ)*x 1 + (787229347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4457067653/10000000000 : ℝ)^39 ≤ (7236211971857/20000000000000 : ℝ)^31 := by
    have hnat : (4457067653 : ℕ)^39*20000000000000^31 ≤ 7236211971857^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457067653 10000000000 7236211971857 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065103253/5000000000 : ℝ)^39 ≤ (16437573604787/50000000000000 : ℝ)^31 := by
    have hnat : (2065103253 : ℕ)^39*50000000000000^31 ≤ 16437573604787^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065103253 5000000000 16437573604787 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (787229347/2000000000 : ℝ)^39 ≤ (15471896453683/50000000000000 : ℝ)^31 := by
    have hnat : (787229347 : ℕ)^39*50000000000000^31 ≤ 15471896453683^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787229347 2000000000 15471896453683 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4457067653/10000000000 : ℝ), (-2065103253/5000000000 : ℝ), (787229347/2000000000 : ℝ)] ![(7236211971857/20000000000000 : ℝ), (16437573604787/50000000000000 : ℝ), (15471896453683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4457067653/10000000000 : ℝ)|^39 ≤ (7236211971857/20000000000000 : ℝ)^31
        have hw : |(4457067653/10000000000 : ℝ)|=(4457067653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065103253/5000000000 : ℝ)|^39 ≤ (16437573604787/50000000000000 : ℝ)^31
        have hw : |(-2065103253/5000000000 : ℝ)|=(2065103253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(787229347/2000000000 : ℝ)|^39 ≤ (15471896453683/50000000000000 : ℝ)^31
        have hw : |(787229347/2000000000 : ℝ)|=(787229347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s0_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9166730003/10000000000 : ℝ)*x 0 + (-489751333/5000000000 : ℝ)*x 1 + (-922898871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9166730003/10000000000 : ℝ)^39 ≤ (44816024804947/50000000000000 : ℝ)^31 := by
    have hnat : (9166730003 : ℕ)^39*50000000000000^31 ≤ 44816024804947^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9166730003 10000000000 44816024804947 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489751333/5000000000 : ℝ)^39 ≤ (2688994914607/50000000000000 : ℝ)^31 := by
    have hnat : (489751333 : ℕ)^39*50000000000000^31 ≤ 2688994914607^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489751333 5000000000 2688994914607 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922898871/10000000000 : ℝ)^39 ≤ (4989960548743/100000000000000 : ℝ)^31 := by
    have hnat : (922898871 : ℕ)^39*100000000000000^31 ≤ 4989960548743^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922898871 10000000000 4989960548743 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9166730003/10000000000 : ℝ), (-489751333/5000000000 : ℝ), (-922898871/10000000000 : ℝ)] ![(44816024804947/50000000000000 : ℝ), (2688994914607/50000000000000 : ℝ), (4989960548743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9166730003/10000000000 : ℝ)|^39 ≤ (44816024804947/50000000000000 : ℝ)^31
        have hw : |(9166730003/10000000000 : ℝ)|=(9166730003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489751333/5000000000 : ℝ)|^39 ≤ (2688994914607/50000000000000 : ℝ)^31
        have hw : |(-489751333/5000000000 : ℝ)|=(489751333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-922898871/10000000000 : ℝ)|^39 ≤ (4989960548743/100000000000000 : ℝ)^31
        have hw : |(-922898871/10000000000 : ℝ)|=(922898871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2505263089/10000000000 : ℝ)*x 0 + (-4945343593/10000000000 : ℝ)*x 1 + (-4945343593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2505263089/10000000000 : ℝ)^39 ≤ (8763724615711/50000000000000 : ℝ)^31 := by
    have hnat : (2505263089 : ℕ)^39*50000000000000^31 ≤ 8763724615711^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505263089 10000000000 8763724615711 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4945343593/10000000000 : ℝ)^39 ≤ (20618137687429/50000000000000 : ℝ)^31 := by
    have hnat : (4945343593 : ℕ)^39*50000000000000^31 ≤ 20618137687429^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945343593 10000000000 20618137687429 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4945343593/10000000000 : ℝ)^39 ≤ (20618137687429/50000000000000 : ℝ)^31 := by
    have hnat : (4945343593 : ℕ)^39*50000000000000^31 ≤ 20618137687429^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945343593 10000000000 20618137687429 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2505263089/10000000000 : ℝ), (-4945343593/10000000000 : ℝ), (-4945343593/10000000000 : ℝ)] ![(8763724615711/50000000000000 : ℝ), (20618137687429/50000000000000 : ℝ), (20618137687429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2505263089/10000000000 : ℝ)|^39 ≤ (8763724615711/50000000000000 : ℝ)^31
        have hw : |(-2505263089/10000000000 : ℝ)|=(2505263089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4945343593/10000000000 : ℝ)|^39 ≤ (20618137687429/50000000000000 : ℝ)^31
        have hw : |(-4945343593/10000000000 : ℝ)|=(4945343593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4945343593/10000000000 : ℝ)|^39 ≤ (20618137687429/50000000000000 : ℝ)^31
        have hw : |(-4945343593/10000000000 : ℝ)|=(4945343593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4522406759/10000000000 : ℝ)*x 0 + (799971201/2000000000 : ℝ)*x 1 + (-799971201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4522406759/10000000000 : ℝ)^39 ≤ (36849597597533/100000000000000 : ℝ)^31 := by
    have hnat : (4522406759 : ℕ)^39*100000000000000^31 ≤ 36849597597533^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522406759 10000000000 36849597597533 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799971201/2000000000 : ℝ)^39 ≤ (15787600597601/50000000000000 : ℝ)^31 := by
    have hnat : (799971201 : ℕ)^39*50000000000000^31 ≤ 15787600597601^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799971201 2000000000 15787600597601 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799971201/2000000000 : ℝ)^39 ≤ (15787600597601/50000000000000 : ℝ)^31 := by
    have hnat : (799971201 : ℕ)^39*50000000000000^31 ≤ 15787600597601^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799971201 2000000000 15787600597601 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4522406759/10000000000 : ℝ), (799971201/2000000000 : ℝ), (-799971201/2000000000 : ℝ)] ![(36849597597533/100000000000000 : ℝ), (15787600597601/50000000000000 : ℝ), (15787600597601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4522406759/10000000000 : ℝ)|^39 ≤ (36849597597533/100000000000000 : ℝ)^31
        have hw : |(4522406759/10000000000 : ℝ)|=(4522406759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(799971201/2000000000 : ℝ)|^39 ≤ (15787600597601/50000000000000 : ℝ)^31
        have hw : |(799971201/2000000000 : ℝ)|=(799971201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-799971201/2000000000 : ℝ)|^39 ≤ (15787600597601/50000000000000 : ℝ)^31
        have hw : |(-799971201/2000000000 : ℝ)|=(799971201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4522406759/10000000000 : ℝ)*x 0 + (-799971201/2000000000 : ℝ)*x 1 + (799971201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4522406759/10000000000 : ℝ)^39 ≤ (36849597597533/100000000000000 : ℝ)^31 := by
    have hnat : (4522406759 : ℕ)^39*100000000000000^31 ≤ 36849597597533^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522406759 10000000000 36849597597533 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799971201/2000000000 : ℝ)^39 ≤ (15787600597601/50000000000000 : ℝ)^31 := by
    have hnat : (799971201 : ℕ)^39*50000000000000^31 ≤ 15787600597601^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799971201 2000000000 15787600597601 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799971201/2000000000 : ℝ)^39 ≤ (15787600597601/50000000000000 : ℝ)^31 := by
    have hnat : (799971201 : ℕ)^39*50000000000000^31 ≤ 15787600597601^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799971201 2000000000 15787600597601 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4522406759/10000000000 : ℝ), (-799971201/2000000000 : ℝ), (799971201/2000000000 : ℝ)] ![(36849597597533/100000000000000 : ℝ), (15787600597601/50000000000000 : ℝ), (15787600597601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4522406759/10000000000 : ℝ)|^39 ≤ (36849597597533/100000000000000 : ℝ)^31
        have hw : |(4522406759/10000000000 : ℝ)|=(4522406759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-799971201/2000000000 : ℝ)|^39 ≤ (15787600597601/50000000000000 : ℝ)^31
        have hw : |(-799971201/2000000000 : ℝ)|=(799971201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(799971201/2000000000 : ℝ)|^39 ≤ (15787600597601/50000000000000 : ℝ)^31
        have hw : |(799971201/2000000000 : ℝ)|=(799971201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316046_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6430957369/10000000000 : ℝ)*x 0 + (-585193413/2000000000 : ℝ)*x 1 + (-585193413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6430957369/10000000000 : ℝ)^39 ≤ (57384998421823/100000000000000 : ℝ)^31 := by
    have hnat : (6430957369 : ℕ)^39*100000000000000^31 ≤ 57384998421823^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6430957369 10000000000 57384998421823 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585193413/2000000000 : ℝ)^39 ≤ (21307500775741/100000000000000 : ℝ)^31 := by
    have hnat : (585193413 : ℕ)^39*100000000000000^31 ≤ 21307500775741^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585193413 2000000000 21307500775741 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585193413/2000000000 : ℝ)^39 ≤ (21307500775741/100000000000000 : ℝ)^31 := by
    have hnat : (585193413 : ℕ)^39*100000000000000^31 ≤ 21307500775741^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585193413 2000000000 21307500775741 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6430957369/10000000000 : ℝ), (-585193413/2000000000 : ℝ), (-585193413/2000000000 : ℝ)] ![(57384998421823/100000000000000 : ℝ), (21307500775741/100000000000000 : ℝ), (21307500775741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6430957369/10000000000 : ℝ)|^39 ≤ (57384998421823/100000000000000 : ℝ)^31
        have hw : |(6430957369/10000000000 : ℝ)|=(6430957369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-585193413/2000000000 : ℝ)|^39 ≤ (21307500775741/100000000000000 : ℝ)^31
        have hw : |(-585193413/2000000000 : ℝ)|=(585193413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-585193413/2000000000 : ℝ)|^39 ≤ (21307500775741/100000000000000 : ℝ)^31
        have hw : |(-585193413/2000000000 : ℝ)|=(585193413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316046 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-200903101/2000000000 : ℝ)*X 0 0+(-5508122927/10000000000 : ℝ)*X 0 1+(-5508122927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1210361009/2500000000 : ℝ)*X 1 0+(958204711/2500000000 : ℝ)*X 1 1+(-958204711/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1627413677/2000000000 : ℝ)*X 0 0+(-1782559423/10000000000 : ℝ)*X 0 1+(-1782559423/10000000000 : ℝ)*X 0 2+(1627413677/2000000000 : ℝ)*X 1 0+(-1782559423/10000000000 : ℝ)*X 1 1+(-1782559423/10000000000 : ℝ)*X 1 2+(1627413677/2000000000 : ℝ)*X 2 0+(-1782559423/10000000000 : ℝ)*X 2 1+(-1782559423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-523251787/5000000000 : ℝ)*X 0 0+(-2841721971/5000000000 : ℝ)*X 0 1+(-2651946001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4738448589/10000000000 : ℝ)*X 1 0+(263183437/625000000 : ℝ)*X 1 1+(-222279867/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4738449751/10000000000 : ℝ)*X 2 0+(-3471708733/10000000000 : ℝ)*X 2 1+(4291637461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4116637249/5000000000 : ℝ)*X 0 0+(-57313549/400000000 : ℝ)*X 0 1+(-1977698289/10000000000 : ℝ)*X 0 2+(4116637249/5000000000 : ℝ)*X 1 0+(-57313549/400000000 : ℝ)*X 1 1+(-1977698289/10000000000 : ℝ)*X 1 2+(4116637249/5000000000 : ℝ)*X 2 0+(-57313549/400000000 : ℝ)*X 2 1+(-1977698289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-182125717/5000000000 : ℝ)*X 0 0+(-276141591/500000000 : ℝ)*X 0 1+(-5861558399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4457065173/10000000000 : ℝ)*X 1 0+(787229693/2000000000 : ℝ)*X 1 1+(-4130207327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((550607929/1000000000 : ℝ)*X 2 0+(-3385524349/10000000000 : ℝ)*X 2 1+(3552436499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((9166730123/10000000000 : ℝ)*X 0 0+(-46144951/500000000 : ℝ)*X 0 1+(-489751153/5000000000 : ℝ)*X 0 2+(9166730123/10000000000 : ℝ)*X 1 0+(-46144951/500000000 : ℝ)*X 1 1+(-489751153/5000000000 : ℝ)*X 1 2+(9166730123/10000000000 : ℝ)*X 2 0+(-46144951/500000000 : ℝ)*X 2 1+(-489751153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-364250533/10000000000 : ℝ)*X 0 0+(-146539003/250000000 : ℝ)*X 0 1+(-2761415259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1101215479/2000000000 : ℝ)*X 1 0+(3552438007/10000000000 : ℝ)*X 1 1+(-3385524971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4457067653/10000000000 : ℝ)*X 2 0+(-2065103253/5000000000 : ℝ)*X 2 1+(787229347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((9166730003/10000000000 : ℝ)*X 0 0+(-489751333/5000000000 : ℝ)*X 0 1+(-922898871/10000000000 : ℝ)*X 0 2+(9166730003/10000000000 : ℝ)*X 1 0+(-489751333/5000000000 : ℝ)*X 1 1+(-922898871/10000000000 : ℝ)*X 1 2+(9166730003/10000000000 : ℝ)*X 2 0+(-489751333/5000000000 : ℝ)*X 2 1+(-922898871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1163/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1163/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4746154491759818015253/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (521045495099/500000000000 : ℝ)*(base39) + (9014279689/100000000000 : ℝ)*(base49) + (2528423/1000000000000 : ℝ)*(base59) + (474262348237/125000000000 : ℝ)*(major_s0_0) + (474262348237/125000000000 : ℝ)*(major_s0_1) + (474262348237/125000000000 : ℝ)*(major_s0_2) + (460930763/1000000000000 : ℝ)*(sp_s0_0) + (223435373/1000000000000 : ℝ)*(sp_s0_6) + (1361820207119/250000000000 : ℝ)*(sp_s0_7) + (5447614295119/1000000000000 : ℝ)*(sp_s0_8) + (5447591797441/1000000000000 : ℝ)*(sp_s0_9) + (2140227314609/1000000000000 : ℝ)*(sp_s0_13) + (3186603/25000000000 : ℝ)*(sp_s0_15) + (149961799/1000000000000 : ℝ)*(sp_s0_22) + (1070225374991/500000000000 : ℝ)*(f.failure) + (5447741759239/1000000000000 : ℝ)*(f.sum) + (59335216548163/625000000000000000000000000 : ℝ)*base63 + (62792562483793/625000000000000000000000000 : ℝ)*base64 + (320447122733793/625000000000000000000000000 : ℝ)*base66 + (756839146048163/1250000000000000000000000000 : ℝ)*base69 + (825013795705577/1250000000000000000000000000 : ℝ)*base71 + (400162013046293/625000000000000000000000000 : ℝ)*base72 + (188933510173163/1250000000000000000000000000 : ℝ)*base75 + (115676655326837/1250000000000000000000000000 : ℝ)*base76 + (99981243108793/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (20313/50000000000000000 : ℝ)*base86 + (20313/50000000000000000 : ℝ)*base88 + (20313/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-34411/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-34411/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19196712642155867050197/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12103379/1000000000000 : ℝ)*(base12) + (83235086029/25000000000 : ℝ)*(base39) + (1678935417751/1000000000000 : ℝ)*(base40) + (2349369/1000000000000 : ℝ)*(base59) + (6639148996199/1000000000000 : ℝ)*(major_s0_0) + (6639148996199/1000000000000 : ℝ)*(major_s0_1) + (6639148996199/1000000000000 : ℝ)*(major_s0_2) + (21502637/500000000000 : ℝ)*(sp_s0_0) + (2669207/50000000000 : ℝ)*(sp_s0_1) + (16200339/500000000000 : ℝ)*(sp_s0_9) + (1906549667853/200000000000 : ℝ)*(sp_s0_14) + (4766375031889/500000000000 : ℝ)*(sp_s0_15) + (238319276181/25000000000 : ℝ)*(sp_s0_16) + (1872746632347/500000000000 : ℝ)*(sp_s0_19) + (1872746632347/500000000000 : ℝ)*(f.failure) + (4766401723959/500000000000 : ℝ)*(f.sum) + (976470543816601/5000000000000000000000000000 : ℝ)*base63 + (1444151541028111/5000000000000000000000000000 : ℝ)*base64 + (1587647081528111/5000000000000000000000000000 : ℝ)*base66 + (2790524538816601/10000000000000000000000000000 : ℝ)*base69 + (8111272775239621/10000000000000000000000000000 : ℝ)*base70 + (1218393834971889/5000000000000000000000000000 : ℝ)*base73 + (3086126394816601/10000000000000000000000000000 : ℝ)*base75 + (5724537851183399/10000000000000000000000000000 : ℝ)*base76 + (896277131471889/2500000000000000000000000000 : ℝ)*base79 + (17821/50000000000000000 : ℝ)*base86 + (17821/50000000000000000 : ℝ)*base88 + (17821/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-34411/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-34411/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11838480665208729643551/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3329417563009/1000000000000 : ℝ)*(base39) + (645979877771/500000000000 : ℝ)*(base40) + (880591/1000000000000 : ℝ)*(base49) + (1866093/500000000000 : ℝ)*(base59) + (6639178599221/1000000000000 : ℝ)*(major_s0_0) + (6639178599221/1000000000000 : ℝ)*(major_s0_1) + (6639178599221/1000000000000 : ℝ)*(major_s0_2) + (260461/200000000000 : ℝ)*(sp_s0_6) + (54688093/500000000000 : ℝ)*(sp_s0_7) + (31239523/500000000000 : ℝ)*(sp_s0_8) + (9532736278469/1000000000000 : ℝ)*(sp_s0_20) + (9532783175609/1000000000000 : ℝ)*(sp_s0_21) + (1906569130931/200000000000 : ℝ)*(sp_s0_22) + (936377165753/250000000000 : ℝ)*(sp_s0_25) + (3745509965317/1000000000000 : ℝ)*(f.failure) + (1906569130931/200000000000 : ℝ)*(f.sum) + (1843006550988021/5000000000000000000000000000 : ℝ)*base62 + (3554266211023731/5000000000000000000000000000 : ℝ)*base65 + (2450780852023731/5000000000000000000000000000 : ℝ)*base67 + (8078550800988021/10000000000000000000000000000 : ℝ)*base68 + (680087655940559/10000000000000000000000000000 : ℝ)*base70 + (4968841420523731/5000000000000000000000000000 : ℝ)*base73 + (8096900866988021/10000000000000000000000000000 : ℝ)*base74 + (1981495746011979/10000000000000000000000000000 : ℝ)*base77 + (1273832472023731/2500000000000000000000000000 : ℝ)*base79 + (95469/100000000000000000 : ℝ)*base87 + (95469/100000000000000000 : ℝ)*base89 + (95469/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1163/25000 : ℝ) ^ (19/4 : ℝ) ≤ (1466015713937/3125000000000000000 : ℝ) := by
    have hpowers : (1163/25000 : ℝ)^19 ≤ (1466015713937/3125000000000000000 : ℝ)^4 := by
      have hnat : (1163 : ℕ)^19*3125000000000000000^4 ≤ 1466015713937^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1163 25000 1466015713937 3125000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1163/25000 : ℝ)) (X := (1466015713937/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3125001466015713937/3125000000000000000 : ℝ) ≤ (312500030863483/312500000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3125001466015713937/3125000000000000000 : ℝ)^4 ≤ (312500030863483/312500000000000 : ℝ)^19 := by
      have hnat : (3125001466015713937 : ℕ)^4*312500000000000^19 ≤ 312500030863483^19*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125001466015713937 3125000000000000000 312500030863483 312500000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500030863483/312500000000000 : ℝ)) (X := (3125001466015713937/3125000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1562501466015713937/1562500000000000000 : ℝ) ≤ (10000001975262547/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (1562501466015713937/1562500000000000000 : ℝ)^4 ≤ (10000001975262547/10000000000000000 : ℝ)^19 := by
      have hnat : (1562501466015713937 : ℕ)^4*10000000000000000^19 ≤ 10000001975262547^19*1562500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562501466015713937 1562500000000000000 10000001975262547 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001975262547/10000000000000000 : ℝ)) (X := (1562501466015713937/1562500000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(30863483/14537500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(987631091/465200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1163/25000 : ℝ)) (alpha := (30863483/14537500000000 : ℝ)) (beta := (987631091/465200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1163/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(30863483/14537500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(987631091/465200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (34411/100000 : ℝ) ^ (19/4 : ℝ) ≤ (629958796510631771/100000000000000000000 : ℝ) := by
    have hpowers : (34411/100000 : ℝ)^19 ≤ (629958796510631771/100000000000000000000 : ℝ)^4 := by
      have hnat : (34411 : ℕ)^19*100000000000000000000^4 ≤ 629958796510631771^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34411 100000 629958796510631771 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34411/100000 : ℝ)) (X := (629958796510631771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100629958796510631771/100000000000000000000 : ℝ) ≤ (5006614717384759/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100629958796510631771/100000000000000000000 : ℝ)^4 ≤ (5006614717384759/5000000000000000 : ℝ)^19 := by
      have hnat : (100629958796510631771 : ℕ)^4*5000000000000000^19 ≤ 5006614717384759^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100629958796510631771 100000000000000000000 5006614717384759 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006614717384759/5000000000000000 : ℝ)) (X := (100629958796510631771/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50629958796510631771/50000000000000000000 : ℝ) ≤ (10026393647406403/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50629958796510631771/50000000000000000000 : ℝ)^4 ≤ (10026393647406403/10000000000000000 : ℝ)^19 := by
      have hnat : (50629958796510631771 : ℕ)^4*10000000000000000^19 ≤ 10026393647406403^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50629958796510631771 50000000000000000000 10026393647406403 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026393647406403/10000000000000000 : ℝ)) (X := (50629958796510631771/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(6614717384759/1720550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2632842527377/688220000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (34411/100000 : ℝ)) (alpha := (6614717384759/1720550000000000 : ℝ)) (beta := (2632842527377/688220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34411/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(6614717384759/1720550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2632842527377/688220000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34411/100000 : ℝ) ^ (19/4 : ℝ) ≤ (629958796510631771/100000000000000000000 : ℝ) := by
    have hpowers : (34411/100000 : ℝ)^19 ≤ (629958796510631771/100000000000000000000 : ℝ)^4 := by
      have hnat : (34411 : ℕ)^19*100000000000000000000^4 ≤ 629958796510631771^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34411 100000 629958796510631771 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34411/100000 : ℝ)) (X := (629958796510631771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100629958796510631771/100000000000000000000 : ℝ) ≤ (5006614717384759/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100629958796510631771/100000000000000000000 : ℝ)^4 ≤ (5006614717384759/5000000000000000 : ℝ)^19 := by
      have hnat : (100629958796510631771 : ℕ)^4*5000000000000000^19 ≤ 5006614717384759^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100629958796510631771 100000000000000000000 5006614717384759 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006614717384759/5000000000000000 : ℝ)) (X := (100629958796510631771/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50629958796510631771/50000000000000000000 : ℝ) ≤ (10026393647406403/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50629958796510631771/50000000000000000000 : ℝ)^4 ≤ (10026393647406403/10000000000000000 : ℝ)^19 := by
      have hnat : (50629958796510631771 : ℕ)^4*10000000000000000^19 ≤ 10026393647406403^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50629958796510631771 50000000000000000000 10026393647406403 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026393647406403/10000000000000000 : ℝ)) (X := (50629958796510631771/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6614717384759/1720550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2632842527377/688220000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (34411/100000 : ℝ)) (alpha := (6614717384759/1720550000000000 : ℝ)) (beta := (2632842527377/688220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34411/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6614717384759/1720550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2632842527377/688220000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2505263089/10000000000 : ℝ)*X 0 0+(-4945343593/10000000000 : ℝ)*X 0 1+(-4945343593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4522406759/10000000000 : ℝ)*X 1 0+(799971201/2000000000 : ℝ)*X 1 1+(-799971201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4522406759/10000000000 : ℝ)*X 2 0+(-799971201/2000000000 : ℝ)*X 2 1+(799971201/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6430957369/10000000000 : ℝ)*X 0 0+(-585193413/2000000000 : ℝ)*X 0 1+(-585193413/2000000000 : ℝ)*X 0 2+(6430957369/10000000000 : ℝ)*X 1 0+(-585193413/2000000000 : ℝ)*X 1 1+(-585193413/2000000000 : ℝ)*X 1 2+(6430957369/10000000000 : ℝ)*X 2 0+(-585193413/2000000000 : ℝ)*X 2 1+(-585193413/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-648451835383805396811475059/86027500000000000000000000 : ℝ) := by norm_num
    linear_combination (11601/1000000000000 : ℝ)*(base27) + (949950817593/1000000000000 : ℝ)*(base39) + (118743852199/250000000000 : ℝ)*(base40) + (230637138717/1000000000000 : ℝ)*(base49) + (230637138717/1000000000000 : ℝ)*(base59) + (753/125000000000 : ℝ)*(ratio_s0_1) + (753/125000000000 : ℝ)*(ratio_s0_2) + (177257/100000 : ℝ)*(major_s1_0) + (177257/100000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2512575766987/1000000000000 : ℝ)*(sp_s1_0) + (2512575766987/1000000000000 : ℝ)*(sp_s1_1) + (2512575766987/1000000000000 : ℝ)*(sp_s1_2) + (999999988399/1000000000000 : ℝ)*(sp_s1_6) + (2512575766987/1000000000000 : ℝ)*(f.sum) + (319490034883/86027500000000000000000000 : ℝ)*base63 + (16300933275057/172055000000000000000000000 : ℝ)*base64 + (16300933275057/172055000000000000000000000 : ℝ)*base66 + (16956032244349/86027500000000000000000000 : ℝ)*base69 + (44409892434849/100049982500000000000000000 : ℝ)*base71 + (459557848319/1163000000000000000000000 : ℝ)*base72 + (16956032244349/86027500000000000000000000 : ℝ)*base75 + (5087723319/1163000000000000000000000 : ℝ)*base76 + (10625927512823/200099965000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p016_b022 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 := by omega
  rcases hc with rfl
  · exact collision_c316046 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b022 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
