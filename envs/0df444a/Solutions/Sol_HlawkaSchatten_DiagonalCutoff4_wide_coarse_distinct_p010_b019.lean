-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:39.661475+00:00
-- url     : https://prove2.me/submissions/d2f93ca6-3604-4d2e-8878-7ff3dca95a24

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
theorem collision_support_c310032_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2822193687/10000000000 : ℝ)*x 0 + (5299262101/10000000000 : ℝ)*x 1 + (-4531098047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2822193687/10000000000 : ℝ)^9 ≤ (19661272418181/100000000000000 : ℝ)^7 := by
    have hnat : (2822193687 : ℕ)^9*100000000000000^7 ≤ 19661272418181^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822193687 10000000000 19661272418181 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5299262101/10000000000 : ℝ)^9 ≤ (44199748711931/100000000000000 : ℝ)^7 := by
    have hnat : (5299262101 : ℕ)^9*100000000000000^7 ≤ 44199748711931^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5299262101 10000000000 44199748711931 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531098047/10000000000 : ℝ)^9 ≤ (18069489427107/50000000000000 : ℝ)^7 := by
    have hnat : (4531098047 : ℕ)^9*50000000000000^7 ≤ 18069489427107^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531098047 10000000000 18069489427107 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2822193687/10000000000 : ℝ), (5299262101/10000000000 : ℝ), (-4531098047/10000000000 : ℝ)] ![(19661272418181/100000000000000 : ℝ), (44199748711931/100000000000000 : ℝ), (18069489427107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2822193687/10000000000 : ℝ)|^9 ≤ (19661272418181/100000000000000 : ℝ)^7
        have hw : |(2822193687/10000000000 : ℝ)|=(2822193687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5299262101/10000000000 : ℝ)|^9 ≤ (44199748711931/100000000000000 : ℝ)^7
        have hw : |(5299262101/10000000000 : ℝ)|=(5299262101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4531098047/10000000000 : ℝ)|^9 ≤ (18069489427107/50000000000000 : ℝ)^7
        have hw : |(-4531098047/10000000000 : ℝ)|=(4531098047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7306524287/10000000000 : ℝ)*x 0 + (-533031579/2000000000 : ℝ)*x 1 + (2278825147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7306524287/10000000000 : ℝ)^9 ≤ (13359834115167/20000000000000 : ℝ)^7 := by
    have hnat : (7306524287 : ℕ)^9*20000000000000^7 ≤ 13359834115167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7306524287 10000000000 13359834115167 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533031579/2000000000 : ℝ)^9 ≤ (1826601393107/10000000000000 : ℝ)^7 := by
    have hnat : (533031579 : ℕ)^9*10000000000000^7 ≤ 1826601393107^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533031579 2000000000 1826601393107 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278825147/10000000000 : ℝ)^9 ≤ (7467407741857/50000000000000 : ℝ)^7 := by
    have hnat : (2278825147 : ℕ)^9*50000000000000^7 ≤ 7467407741857^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278825147 10000000000 7467407741857 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7306524287/10000000000 : ℝ), (-533031579/2000000000 : ℝ), (2278825147/10000000000 : ℝ)] ![(13359834115167/20000000000000 : ℝ), (1826601393107/10000000000000 : ℝ), (7467407741857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7306524287/10000000000 : ℝ)|^9 ≤ (13359834115167/20000000000000 : ℝ)^7
        have hw : |(7306524287/10000000000 : ℝ)|=(7306524287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533031579/2000000000 : ℝ)|^9 ≤ (1826601393107/10000000000000 : ℝ)^7
        have hw : |(-533031579/2000000000 : ℝ)|=(533031579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2278825147/10000000000 : ℝ)|^9 ≤ (7467407741857/50000000000000 : ℝ)^7
        have hw : |(2278825147/10000000000 : ℝ)|=(2278825147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^9 ≤ (1 : ℝ)^7 := by
    have hnat : (1 : ℕ)^9*1^7 ≤ 1^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^9 ≤ (1 : ℝ)^7
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1751283821/5000000000 : ℝ)*x 0 + (-4232951407/10000000000 : ℝ)*x 1 + (-4992223359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1751283821/5000000000 : ℝ)^9 ≤ (5190883117659/20000000000000 : ℝ)^7 := by
    have hnat : (1751283821 : ℕ)^9*20000000000000^7 ≤ 5190883117659^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751283821 5000000000 5190883117659 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232951407/10000000000 : ℝ)^9 ≤ (33110819914143/100000000000000 : ℝ)^7 := by
    have hnat : (4232951407 : ℕ)^9*100000000000000^7 ≤ 33110819914143^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232951407 10000000000 33110819914143 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992223359/10000000000 : ℝ)^9 ≤ (10233691121417/25000000000000 : ℝ)^7 := by
    have hnat : (4992223359 : ℕ)^9*25000000000000^7 ≤ 10233691121417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992223359 10000000000 10233691121417 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1751283821/5000000000 : ℝ), (-4232951407/10000000000 : ℝ), (-4992223359/10000000000 : ℝ)] ![(5190883117659/20000000000000 : ℝ), (33110819914143/100000000000000 : ℝ), (10233691121417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1751283821/5000000000 : ℝ)|^9 ≤ (5190883117659/20000000000000 : ℝ)^7
        have hw : |(1751283821/5000000000 : ℝ)|=(1751283821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4232951407/10000000000 : ℝ)|^9 ≤ (33110819914143/100000000000000 : ℝ)^7
        have hw : |(-4232951407/10000000000 : ℝ)|=(4232951407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4992223359/10000000000 : ℝ)|^9 ≤ (10233691121417/25000000000000 : ℝ)^7
        have hw : |(-4992223359/10000000000 : ℝ)|=(4992223359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1262496639/5000000000 : ℝ)*x 0 + (-4709645161/10000000000 : ℝ)*x 1 + (-2685920117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1262496639/5000000000 : ℝ)^9 ≤ (3408061549071/20000000000000 : ℝ)^7 := by
    have hnat : (1262496639 : ℕ)^9*20000000000000^7 ≤ 3408061549071^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262496639 5000000000 3408061549071 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4709645161/10000000000 : ℝ)^9 ≤ (37980111974367/100000000000000 : ℝ)^7 := by
    have hnat : (4709645161 : ℕ)^9*100000000000000^7 ≤ 37980111974367^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709645161 10000000000 37980111974367 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2685920117/5000000000 : ℝ)^9 ≤ (8995916053143/20000000000000 : ℝ)^7 := by
    have hnat : (2685920117 : ℕ)^9*20000000000000^7 ≤ 8995916053143^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685920117 5000000000 8995916053143 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1262496639/5000000000 : ℝ), (-4709645161/10000000000 : ℝ), (-2685920117/5000000000 : ℝ)] ![(3408061549071/20000000000000 : ℝ), (37980111974367/100000000000000 : ℝ), (8995916053143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1262496639/5000000000 : ℝ)|^9 ≤ (3408061549071/20000000000000 : ℝ)^7
        have hw : |(-1262496639/5000000000 : ℝ)|=(1262496639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4709645161/10000000000 : ℝ)|^9 ≤ (37980111974367/100000000000000 : ℝ)^7
        have hw : |(-4709645161/10000000000 : ℝ)|=(4709645161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2685920117/5000000000 : ℝ)|^9 ≤ (8995916053143/20000000000000 : ℝ)^7
        have hw : |(-2685920117/5000000000 : ℝ)|=(2685920117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1393310339/5000000000 : ℝ)*x 0 + (2287023/4000000 : ℝ)*x 1 + (-1028557683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1393310339/5000000000 : ℝ)^9 ≤ (19343215546249/100000000000000 : ℝ)^7 := by
    have hnat : (1393310339 : ℕ)^9*100000000000000^7 ≤ 19343215546249^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393310339 5000000000 19343215546249 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287023/4000000 : ℝ)^9 ≤ (48735129452943/100000000000000 : ℝ)^7 := by
    have hnat : (2287023 : ℕ)^9*100000000000000^7 ≤ 48735129452943^7*4000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287023 4000000 48735129452943 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028557683/2500000000 : ℝ)^9 ≤ (31921654981471/100000000000000 : ℝ)^7 := by
    have hnat : (1028557683 : ℕ)^9*100000000000000^7 ≤ 31921654981471^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028557683 2500000000 31921654981471 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1393310339/5000000000 : ℝ), (2287023/4000000 : ℝ), (-1028557683/2500000000 : ℝ)] ![(19343215546249/100000000000000 : ℝ), (48735129452943/100000000000000 : ℝ), (31921654981471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1393310339/5000000000 : ℝ)|^9 ≤ (19343215546249/100000000000000 : ℝ)^7
        have hw : |(1393310339/5000000000 : ℝ)|=(1393310339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287023/4000000 : ℝ)|^9 ≤ (48735129452943/100000000000000 : ℝ)^7
        have hw : |(2287023/4000000 : ℝ)|=(2287023/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028557683/2500000000 : ℝ)|^9 ≤ (31921654981471/100000000000000 : ℝ)^7
        have hw : |(-1028557683/2500000000 : ℝ)|=(1028557683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3635890163/5000000000 : ℝ)*x 0 + (-120539439/500000000 : ℝ)*x 1 + (2583897413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3635890163/5000000000 : ℝ)^9 ≤ (2074720309919/3125000000000 : ℝ)^7 := by
    have hnat : (3635890163 : ℕ)^9*3125000000000^7 ≤ 2074720309919^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635890163 5000000000 2074720309919 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120539439/500000000 : ℝ)^9 ≤ (16055846508917/100000000000000 : ℝ)^7 := by
    have hnat : (120539439 : ℕ)^9*100000000000000^7 ≤ 16055846508917^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120539439 500000000 16055846508917 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583897413/10000000000 : ℝ)^9 ≤ (4388275887729/25000000000000 : ℝ)^7 := by
    have hnat : (2583897413 : ℕ)^9*25000000000000^7 ≤ 4388275887729^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583897413 10000000000 4388275887729 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3635890163/5000000000 : ℝ), (-120539439/500000000 : ℝ), (2583897413/10000000000 : ℝ)] ![(2074720309919/3125000000000 : ℝ), (16055846508917/100000000000000 : ℝ), (4388275887729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3635890163/5000000000 : ℝ)|^9 ≤ (2074720309919/3125000000000 : ℝ)^7
        have hw : |(3635890163/5000000000 : ℝ)|=(3635890163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120539439/500000000 : ℝ)|^9 ≤ (16055846508917/100000000000000 : ℝ)^7
        have hw : |(-120539439/500000000 : ℝ)|=(120539439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583897413/10000000000 : ℝ)|^9 ≤ (4388275887729/25000000000000 : ℝ)^7
        have hw : |(2583897413/10000000000 : ℝ)|=(2583897413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (798874509/2000000000 : ℝ)*x 0 + (-415815893/1250000000 : ℝ)*x 1 + (-2685920117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798874509/2000000000 : ℝ)^9 ≤ (15365501331351/50000000000000 : ℝ)^7 := by
    have hnat : (798874509 : ℕ)^9*50000000000000^7 ≤ 15365501331351^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798874509 2000000000 15365501331351 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415815893/1250000000 : ℝ)^9 ≤ (24289417063377/100000000000000 : ℝ)^7 := by
    have hnat : (415815893 : ℕ)^9*100000000000000^7 ≤ 24289417063377^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415815893 1250000000 24289417063377 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2685920117/5000000000 : ℝ)^9 ≤ (8995916053143/20000000000000 : ℝ)^7 := by
    have hnat : (2685920117 : ℕ)^9*20000000000000^7 ≤ 8995916053143^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685920117 5000000000 8995916053143 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(798874509/2000000000 : ℝ), (-415815893/1250000000 : ℝ), (-2685920117/5000000000 : ℝ)] ![(15365501331351/50000000000000 : ℝ), (24289417063377/100000000000000 : ℝ), (8995916053143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(798874509/2000000000 : ℝ)|^9 ≤ (15365501331351/50000000000000 : ℝ)^7
        have hw : |(798874509/2000000000 : ℝ)|=(798874509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415815893/1250000000 : ℝ)|^9 ≤ (24289417063377/100000000000000 : ℝ)^7
        have hw : |(-415815893/1250000000 : ℝ)|=(415815893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2685920117/5000000000 : ℝ)|^9 ≤ (8995916053143/20000000000000 : ℝ)^7
        have hw : |(-2685920117/5000000000 : ℝ)|=(2685920117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102973061/10000000000 : ℝ)*x 0 + (-886559187/2000000000 : ℝ)*x 1 + (-2979468471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102973061/10000000000 : ℝ)^9 ≤ (841855674813/6250000000000 : ℝ)^7 := by
    have hnat : (2102973061 : ℕ)^9*6250000000000^7 ≤ 841855674813^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102973061 10000000000 841855674813 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886559187/2000000000 : ℝ)^9 ≤ (8783518697229/25000000000000 : ℝ)^7 := by
    have hnat : (886559187 : ℕ)^9*25000000000000^7 ≤ 8783518697229^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886559187 2000000000 8783518697229 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2979468471/5000000000 : ℝ)^9 ≤ (25698117196399/50000000000000 : ℝ)^7 := by
    have hnat : (2979468471 : ℕ)^9*50000000000000^7 ≤ 25698117196399^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979468471 5000000000 25698117196399 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102973061/10000000000 : ℝ), (-886559187/2000000000 : ℝ), (-2979468471/5000000000 : ℝ)] ![(841855674813/6250000000000 : ℝ), (8783518697229/25000000000000 : ℝ), (25698117196399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102973061/10000000000 : ℝ)|^9 ≤ (841855674813/6250000000000 : ℝ)^7
        have hw : |(-2102973061/10000000000 : ℝ)|=(2102973061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-886559187/2000000000 : ℝ)|^9 ≤ (8783518697229/25000000000000 : ℝ)^7
        have hw : |(-886559187/2000000000 : ℝ)|=(886559187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2979468471/5000000000 : ℝ)|^9 ≤ (25698117196399/50000000000000 : ℝ)^7
        have hw : |(-2979468471/5000000000 : ℝ)|=(2979468471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2272671019/10000000000 : ℝ)*x 0 + (5616498817/10000000000 : ℝ)*x 1 + (-4661978263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272671019/10000000000 : ℝ)^9 ≤ (1488297940231/10000000000000 : ℝ)^7 := by
    have hnat : (2272671019 : ℕ)^9*10000000000000^7 ≤ 1488297940231^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272671019 10000000000 1488297940231 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616498817/10000000000 : ℝ)^9 ≤ (952608452663/2000000000000 : ℝ)^7 := by
    have hnat : (5616498817 : ℕ)^9*2000000000000^7 ≤ 952608452663^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616498817 10000000000 952608452663 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4661978263/10000000000 : ℝ)^9 ≤ (37486597946721/100000000000000 : ℝ)^7 := by
    have hnat : (4661978263 : ℕ)^9*100000000000000^7 ≤ 37486597946721^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661978263 10000000000 37486597946721 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272671019/10000000000 : ℝ), (5616498817/10000000000 : ℝ), (-4661978263/10000000000 : ℝ)] ![(1488297940231/10000000000000 : ℝ), (952608452663/2000000000000 : ℝ), (37486597946721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272671019/10000000000 : ℝ)|^9 ≤ (1488297940231/10000000000000 : ℝ)^7
        have hw : |(2272671019/10000000000 : ℝ)|=(2272671019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616498817/10000000000 : ℝ)|^9 ≤ (952608452663/2000000000000 : ℝ)^7
        have hw : |(5616498817/10000000000 : ℝ)|=(5616498817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4661978263/10000000000 : ℝ)|^9 ≤ (37486597946721/100000000000000 : ℝ)^7
        have hw : |(-4661978263/10000000000 : ℝ)|=(4661978263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8064167603/10000000000 : ℝ)*x 0 + (-263682841/1250000000 : ℝ)*x 1 + (875480411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8064167603/10000000000 : ℝ)^9 ≤ (303334818537/400000000000 : ℝ)^7 := by
    have hnat : (8064167603 : ℕ)^9*400000000000^7 ≤ 303334818537^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8064167603 10000000000 303334818537 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263682841/1250000000 : ℝ)^9 ≤ (6761578668183/50000000000000 : ℝ)^7 := by
    have hnat : (263682841 : ℕ)^9*50000000000000^7 ≤ 6761578668183^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263682841 1250000000 6761578668183 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875480411/5000000000 : ℝ)^9 ≤ (10643138021221/100000000000000 : ℝ)^7 := by
    have hnat : (875480411 : ℕ)^9*100000000000000^7 ≤ 10643138021221^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875480411 5000000000 10643138021221 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8064167603/10000000000 : ℝ), (-263682841/1250000000 : ℝ), (875480411/5000000000 : ℝ)] ![(303334818537/400000000000 : ℝ), (6761578668183/50000000000000 : ℝ), (10643138021221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8064167603/10000000000 : ℝ)|^9 ≤ (303334818537/400000000000 : ℝ)^7
        have hw : |(8064167603/10000000000 : ℝ)|=(8064167603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263682841/1250000000 : ℝ)|^9 ≤ (6761578668183/50000000000000 : ℝ)^7
        have hw : |(-263682841/1250000000 : ℝ)|=(263682841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875480411/5000000000 : ℝ)|^9 ≤ (10643138021221/100000000000000 : ℝ)^7
        have hw : |(875480411/5000000000 : ℝ)|=(875480411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (908984551/2000000000 : ℝ)*x 0 + (-349391743/1000000000 : ℝ)*x 1 + (-4696817529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908984551/2000000000 : ℝ)^9 ≤ (36280806851351/100000000000000 : ℝ)^7 := by
    have hnat : (908984551 : ℕ)^9*100000000000000^7 ≤ 36280806851351^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908984551 2000000000 36280806851351 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349391743/1000000000 : ℝ)^9 ≤ (6468007909959/25000000000000 : ℝ)^7 := by
    have hnat : (349391743 : ℕ)^9*25000000000000^7 ≤ 6468007909959^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349391743 1000000000 6468007909959 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696817529/10000000000 : ℝ)^9 ≤ (18923580750333/50000000000000 : ℝ)^7 := by
    have hnat : (4696817529 : ℕ)^9*50000000000000^7 ≤ 18923580750333^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696817529 10000000000 18923580750333 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(908984551/2000000000 : ℝ), (-349391743/1000000000 : ℝ), (-4696817529/10000000000 : ℝ)] ![(36280806851351/100000000000000 : ℝ), (6468007909959/25000000000000 : ℝ), (18923580750333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(908984551/2000000000 : ℝ)|^9 ≤ (36280806851351/100000000000000 : ℝ)^7
        have hw : |(908984551/2000000000 : ℝ)|=(908984551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349391743/1000000000 : ℝ)|^9 ≤ (6468007909959/25000000000000 : ℝ)^7
        have hw : |(-349391743/1000000000 : ℝ)|=(349391743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4696817529/10000000000 : ℝ)|^9 ≤ (18923580750333/50000000000000 : ℝ)^7
        have hw : |(-4696817529/10000000000 : ℝ)|=(4696817529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2702187427/10000000000 : ℝ)*x 0 + (-5097371773/10000000000 : ℝ)*x 1 + (-302640187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702187427/10000000000 : ℝ)^9 ≤ (18592956792049/100000000000000 : ℝ)^7 := by
    have hnat : (2702187427 : ℕ)^9*100000000000000^7 ≤ 18592956792049^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702187427 10000000000 18592956792049 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097371773/10000000000 : ℝ)^9 ≤ (5255826043821/12500000000000 : ℝ)^7 := by
    have hnat : (5097371773 : ℕ)^9*12500000000000^7 ≤ 5255826043821^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097371773 10000000000 5255826043821 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302640187/625000000 : ℝ)^9 ≤ (39360434834727/100000000000000 : ℝ)^7 := by
    have hnat : (302640187 : ℕ)^9*100000000000000^7 ≤ 39360434834727^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302640187 625000000 39360434834727 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2702187427/10000000000 : ℝ), (-5097371773/10000000000 : ℝ), (-302640187/625000000 : ℝ)] ![(18592956792049/100000000000000 : ℝ), (5255826043821/12500000000000 : ℝ), (39360434834727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2702187427/10000000000 : ℝ)|^9 ≤ (18592956792049/100000000000000 : ℝ)^7
        have hw : |(-2702187427/10000000000 : ℝ)|=(2702187427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5097371773/10000000000 : ℝ)|^9 ≤ (5255826043821/12500000000000 : ℝ)^7
        have hw : |(-5097371773/10000000000 : ℝ)|=(5097371773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302640187/625000000 : ℝ)|^9 ≤ (39360434834727/100000000000000 : ℝ)^7
        have hw : |(-302640187/625000000 : ℝ)|=(302640187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2128153893/10000000000 : ℝ)*x 0 + (134735441/250000000 : ℝ)*x 1 + (-1002595411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128153893/10000000000 : ℝ)^9 ≤ (6838705469441/50000000000000 : ℝ)^7 := by
    have hnat : (2128153893 : ℕ)^9*50000000000000^7 ≤ 6838705469441^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128153893 10000000000 6838705469441 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134735441/250000000 : ℝ)^9 ≤ (45168899338699/100000000000000 : ℝ)^7 := by
    have hnat : (134735441 : ℕ)^9*100000000000000^7 ≤ 45168899338699^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134735441 250000000 45168899338699 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002595411/2000000000 : ℝ)^9 ≤ (10288422426907/25000000000000 : ℝ)^7 := by
    have hnat : (1002595411 : ℕ)^9*25000000000000^7 ≤ 10288422426907^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002595411 2000000000 10288422426907 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128153893/10000000000 : ℝ), (134735441/250000000 : ℝ), (-1002595411/2000000000 : ℝ)] ![(6838705469441/50000000000000 : ℝ), (45168899338699/100000000000000 : ℝ), (10288422426907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128153893/10000000000 : ℝ)|^9 ≤ (6838705469441/50000000000000 : ℝ)^7
        have hw : |(2128153893/10000000000 : ℝ)|=(2128153893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134735441/250000000 : ℝ)|^9 ≤ (45168899338699/100000000000000 : ℝ)^7
        have hw : |(134735441/250000000 : ℝ)|=(134735441/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002595411/2000000000 : ℝ)|^9 ≤ (10288422426907/25000000000000 : ℝ)^7
        have hw : |(-1002595411/2000000000 : ℝ)|=(1002595411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4216821549/5000000000 : ℝ)*x 0 + (-106621041/625000000 : ℝ)*x 1 + (1586780221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216821549/5000000000 : ℝ)^9 ≤ (20082451085059/25000000000000 : ℝ)^7 := by
    have hnat : (4216821549 : ℕ)^9*25000000000000^7 ≤ 20082451085059^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216821549 5000000000 20082451085059 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106621041/625000000 : ℝ)^9 ≤ (643285477897/6250000000000 : ℝ)^7 := by
    have hnat : (106621041 : ℕ)^9*6250000000000^7 ≤ 643285477897^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106621041 625000000 643285477897 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586780221/10000000000 : ℝ)^9 ≤ (1875525600213/20000000000000 : ℝ)^7 := by
    have hnat : (1586780221 : ℕ)^9*20000000000000^7 ≤ 1875525600213^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586780221 10000000000 1875525600213 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216821549/5000000000 : ℝ), (-106621041/625000000 : ℝ), (1586780221/10000000000 : ℝ)] ![(20082451085059/25000000000000 : ℝ), (643285477897/6250000000000 : ℝ), (1875525600213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216821549/5000000000 : ℝ)|^9 ≤ (20082451085059/25000000000000 : ℝ)^7
        have hw : |(4216821549/5000000000 : ℝ)|=(4216821549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106621041/625000000 : ℝ)|^9 ≤ (643285477897/6250000000000 : ℝ)^7
        have hw : |(-106621041/625000000 : ℝ)|=(106621041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586780221/10000000000 : ℝ)|^9 ≤ (1875525600213/20000000000000 : ℝ)^7
        have hw : |(1586780221/10000000000 : ℝ)|=(1586780221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2702187427/10000000000 : ℝ)*x 0 + (-5097371773/10000000000 : ℝ)*x 1 + (-302640187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702187427/10000000000 : ℝ)^9 ≤ (18592956792049/100000000000000 : ℝ)^7 := by
    have hnat : (2702187427 : ℕ)^9*100000000000000^7 ≤ 18592956792049^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702187427 10000000000 18592956792049 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097371773/10000000000 : ℝ)^9 ≤ (5255826043821/12500000000000 : ℝ)^7 := by
    have hnat : (5097371773 : ℕ)^9*12500000000000^7 ≤ 5255826043821^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097371773 10000000000 5255826043821 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302640187/625000000 : ℝ)^9 ≤ (39360434834727/100000000000000 : ℝ)^7 := by
    have hnat : (302640187 : ℕ)^9*100000000000000^7 ≤ 39360434834727^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302640187 625000000 39360434834727 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702187427/10000000000 : ℝ), (-5097371773/10000000000 : ℝ), (-302640187/625000000 : ℝ)] ![(18592956792049/100000000000000 : ℝ), (5255826043821/12500000000000 : ℝ), (39360434834727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702187427/10000000000 : ℝ)|^9 ≤ (18592956792049/100000000000000 : ℝ)^7
        have hw : |(2702187427/10000000000 : ℝ)|=(2702187427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5097371773/10000000000 : ℝ)|^9 ≤ (5255826043821/12500000000000 : ℝ)^7
        have hw : |(-5097371773/10000000000 : ℝ)|=(5097371773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302640187/625000000 : ℝ)|^9 ≤ (39360434834727/100000000000000 : ℝ)^7
        have hw : |(-302640187/625000000 : ℝ)|=(302640187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3364360023/10000000000 : ℝ)*x 0 + (-417990509/1000000000 : ℝ)*x 1 + (-2583033329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3364360023/10000000000 : ℝ)^9 ≤ (24645165516309/100000000000000 : ℝ)^7 := by
    have hnat : (3364360023 : ℕ)^9*100000000000000^7 ≤ 24645165516309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364360023 10000000000 24645165516309 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417990509/1000000000 : ℝ)^9 ≤ (32578287768599/100000000000000 : ℝ)^7 := by
    have hnat : (417990509 : ℕ)^9*100000000000000^7 ≤ 32578287768599^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417990509 1000000000 32578287768599 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583033329/5000000000 : ℝ)^9 ≤ (5347068336379/12500000000000 : ℝ)^7 := by
    have hnat : (2583033329 : ℕ)^9*12500000000000^7 ≤ 5347068336379^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583033329 5000000000 5347068336379 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3364360023/10000000000 : ℝ), (-417990509/1000000000 : ℝ), (-2583033329/5000000000 : ℝ)] ![(24645165516309/100000000000000 : ℝ), (32578287768599/100000000000000 : ℝ), (5347068336379/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3364360023/10000000000 : ℝ)|^9 ≤ (24645165516309/100000000000000 : ℝ)^7
        have hw : |(-3364360023/10000000000 : ℝ)|=(3364360023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417990509/1000000000 : ℝ)|^9 ≤ (32578287768599/100000000000000 : ℝ)^7
        have hw : |(-417990509/1000000000 : ℝ)|=(417990509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2583033329/5000000000 : ℝ)|^9 ≤ (5347068336379/12500000000000 : ℝ)^7
        have hw : |(-2583033329/5000000000 : ℝ)|=(2583033329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1931455303/5000000000 : ℝ)*x 0 + (964638663/2000000000 : ℝ)*x 1 + (-4062019709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931455303/5000000000 : ℝ)^9 ≤ (29436778132143/100000000000000 : ℝ)^7 := by
    have hnat : (1931455303 : ℕ)^9*100000000000000^7 ≤ 29436778132143^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931455303 5000000000 29436778132143 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964638663/2000000000 : ℝ)^9 ≤ (39161458686703/100000000000000 : ℝ)^7 := by
    have hnat : (964638663 : ℕ)^9*100000000000000^7 ≤ 39161458686703^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964638663 2000000000 39161458686703 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4062019709/10000000000 : ℝ)^9 ≤ (7850440791309/25000000000000 : ℝ)^7 := by
    have hnat : (4062019709 : ℕ)^9*25000000000000^7 ≤ 7850440791309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4062019709 10000000000 7850440791309 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1931455303/5000000000 : ℝ), (964638663/2000000000 : ℝ), (-4062019709/10000000000 : ℝ)] ![(29436778132143/100000000000000 : ℝ), (39161458686703/100000000000000 : ℝ), (7850440791309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1931455303/5000000000 : ℝ)|^9 ≤ (29436778132143/100000000000000 : ℝ)^7
        have hw : |(1931455303/5000000000 : ℝ)|=(1931455303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964638663/2000000000 : ℝ)|^9 ≤ (39161458686703/100000000000000 : ℝ)^7
        have hw : |(964638663/2000000000 : ℝ)|=(964638663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4062019709/10000000000 : ℝ)|^9 ≤ (7850440791309/25000000000000 : ℝ)^7
        have hw : |(-4062019709/10000000000 : ℝ)|=(4062019709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5415621163/10000000000 : ℝ)*x 0 + (-3948051657/10000000000 : ℝ)*x 1 + (3324988777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415621163/10000000000 : ℝ)^9 ≤ (363611634833/800000000000 : ℝ)^7 := by
    have hnat : (5415621163 : ℕ)^9*800000000000^7 ≤ 363611634833^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415621163 10000000000 363611634833 800000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3948051657/10000000000 : ℝ)^9 ≤ (30273569719029/100000000000000 : ℝ)^7 := by
    have hnat : (3948051657 : ℕ)^9*100000000000000^7 ≤ 30273569719029^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948051657 10000000000 30273569719029 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3324988777/10000000000 : ℝ)^9 ≤ (12137487957183/50000000000000 : ℝ)^7 := by
    have hnat : (3324988777 : ℕ)^9*50000000000000^7 ≤ 12137487957183^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3324988777 10000000000 12137487957183 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415621163/10000000000 : ℝ), (-3948051657/10000000000 : ℝ), (3324988777/10000000000 : ℝ)] ![(363611634833/800000000000 : ℝ), (30273569719029/100000000000000 : ℝ), (12137487957183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415621163/10000000000 : ℝ)|^9 ≤ (363611634833/800000000000 : ℝ)^7
        have hw : |(5415621163/10000000000 : ℝ)|=(5415621163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3948051657/10000000000 : ℝ)|^9 ≤ (30273569719029/100000000000000 : ℝ)^7
        have hw : |(-3948051657/10000000000 : ℝ)|=(3948051657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3324988777/10000000000 : ℝ)|^9 ≤ (12137487957183/50000000000000 : ℝ)^7
        have hw : |(3324988777/10000000000 : ℝ)|=(3324988777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310032_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4411178997/10000000000 : ℝ)*x 0 + (-3729767427/10000000000 : ℝ)*x 1 + (-4609728387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4411178997/10000000000 : ℝ)^9 ≤ (34913941147673/100000000000000 : ℝ)^7 := by
    have hnat : (4411178997 : ℕ)^9*100000000000000^7 ≤ 34913941147673^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411178997 10000000000 34913941147673 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3729767427/10000000000 : ℝ)^9 ≤ (7034692497299/25000000000000 : ℝ)^7 := by
    have hnat : (3729767427 : ℕ)^9*25000000000000^7 ≤ 7034692497299^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729767427 10000000000 7034692497299 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4609728387/10000000000 : ℝ)^9 ≤ (36947288849273/100000000000000 : ℝ)^7 := by
    have hnat : (4609728387 : ℕ)^9*100000000000000^7 ≤ 36947288849273^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609728387 10000000000 36947288849273 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4411178997/10000000000 : ℝ), (-3729767427/10000000000 : ℝ), (-4609728387/10000000000 : ℝ)] ![(34913941147673/100000000000000 : ℝ), (7034692497299/25000000000000 : ℝ), (36947288849273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4411178997/10000000000 : ℝ)|^9 ≤ (34913941147673/100000000000000 : ℝ)^7
        have hw : |(4411178997/10000000000 : ℝ)|=(4411178997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3729767427/10000000000 : ℝ)|^9 ≤ (7034692497299/25000000000000 : ℝ)^7
        have hw : |(-3729767427/10000000000 : ℝ)|=(3729767427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4609728387/10000000000 : ℝ)|^9 ≤ (36947288849273/100000000000000 : ℝ)^7
        have hw : |(-4609728387/10000000000 : ℝ)|=(4609728387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310032 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2822193687/10000000000 : ℝ)*X 1 0+(5299262101/10000000000 : ℝ)*X 1 1+(-4531098047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((7306524287/10000000000 : ℝ)*X 2 0+(-533031579/2000000000 : ℝ)*X 2 1+(2278825147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1751283821/5000000000 : ℝ)*X 0 0+(-4232951407/10000000000 : ℝ)*X 0 1+(-4992223359/10000000000 : ℝ)*X 0 2+(1751283821/5000000000 : ℝ)*X 1 0+(-4232951407/10000000000 : ℝ)*X 1 1+(-4992223359/10000000000 : ℝ)*X 1 2+(1751283821/5000000000 : ℝ)*X 2 0+(-4232951407/10000000000 : ℝ)*X 2 1+(-4992223359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1262496639/5000000000 : ℝ)*X 0 0+(-4709645161/10000000000 : ℝ)*X 0 1+(-2685920117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1393310339/5000000000 : ℝ)*X 1 0+(2287023/4000000 : ℝ)*X 1 1+(-1028557683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3635890163/5000000000 : ℝ)*X 2 0+(-120539439/500000000 : ℝ)*X 2 1+(2583897413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((798874509/2000000000 : ℝ)*X 0 0+(-415815893/1250000000 : ℝ)*X 0 1+(-2685920117/5000000000 : ℝ)*X 0 2+(798874509/2000000000 : ℝ)*X 1 0+(-415815893/1250000000 : ℝ)*X 1 1+(-2685920117/5000000000 : ℝ)*X 1 2+(798874509/2000000000 : ℝ)*X 2 0+(-415815893/1250000000 : ℝ)*X 2 1+(-2685920117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2102973061/10000000000 : ℝ)*X 0 0+(-886559187/2000000000 : ℝ)*X 0 1+(-2979468471/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2272671019/10000000000 : ℝ)*X 1 0+(5616498817/10000000000 : ℝ)*X 1 1+(-4661978263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8064167603/10000000000 : ℝ)*X 2 0+(-263682841/1250000000 : ℝ)*X 2 1+(875480411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((908984551/2000000000 : ℝ)*X 0 0+(-349391743/1000000000 : ℝ)*X 0 1+(-4696817529/10000000000 : ℝ)*X 0 2+(908984551/2000000000 : ℝ)*X 1 0+(-349391743/1000000000 : ℝ)*X 1 1+(-4696817529/10000000000 : ℝ)*X 1 2+(908984551/2000000000 : ℝ)*X 2 0+(-349391743/1000000000 : ℝ)*X 2 1+(-4696817529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2702187427/10000000000 : ℝ)*X 0 0+(-5097371773/10000000000 : ℝ)*X 0 1+(-302640187/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2128153893/10000000000 : ℝ)*X 1 0+(134735441/250000000 : ℝ)*X 1 1+(-1002595411/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4216821549/5000000000 : ℝ)*X 2 0+(-106621041/625000000 : ℝ)*X 2 1+(1586780221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((2702187427/10000000000 : ℝ)*X 0 0+(-5097371773/10000000000 : ℝ)*X 0 1+(-302640187/625000000 : ℝ)*X 0 2+(2702187427/10000000000 : ℝ)*X 1 0+(-5097371773/10000000000 : ℝ)*X 1 1+(-302640187/625000000 : ℝ)*X 1 2+(2702187427/10000000000 : ℝ)*X 2 0+(-5097371773/10000000000 : ℝ)*X 2 1+(-302640187/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5281/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5281/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5114198886451096001793/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433376642163/1000000000000 : ℝ)*(base1) + (190380564171/1000000000000 : ℝ)*(base39) + (58239950033/500000000000 : ℝ)*(base50) + (1798687/500000000000 : ℝ)*(base59) + (350319630009/500000000000 : ℝ)*(base60) + (295557421291/100000000000 : ℝ)*(major_s0_0) + (295557421291/100000000000 : ℝ)*(major_s0_1) + (295557421291/100000000000 : ℝ)*(major_s0_2) + (14337513/200000000000 : ℝ)*(sp_s0_6) + (9035283319/2000000000 : ℝ)*(sp_s0_7) + (510547786631/125000000000 : ℝ)*(sp_s0_8) + (510547786631/125000000000 : ℝ)*(sp_s0_9) + (1393314393573/1000000000000 : ℝ)*(sp_s0_13) + (117275711/1000000000000 : ℝ)*(sp_s0_14) + (1826762723301/1000000000000 : ℝ)*(f.failure) + (510547786631/125000000000 : ℝ)*(f.sum) + (1097259339/2500000000000000000000 : ℝ)*base63 + (274673204916069/1000000000000000000000000000 : ℝ)*base64 + (705953987783931/1000000000000000000000000000 : ℝ)*base67 + (89341314334727/1000000000000000000000000000 : ℝ)*base68 + (412708237490671/500000000000000000000000000 : ℝ)*base70 + (754804385416069/1000000000000000000000000000 : ℝ)*base73 + (656885707865273/1000000000000000000000000000 : ℝ)*base74 + (586774249134727/1000000000000000000000000000 : ℝ)*base77 + (3560162093/10000000000000000000000 : ℝ)*base79 + (38693/100000000000000000 : ℝ)*base87 + (38693/100000000000000000 : ℝ)*base89 + (38693/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-23207/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5675490860877405106239/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304662712417/500000000000 : ℝ)*(base40) + (1043398652537/1000000000000 : ℝ)*(base60) + (3963740288797/500000000000 : ℝ)*(major_s0_0) + (2235703954379/500000000000 : ℝ)*(major_s0_1) + (2235703954379/500000000000 : ℝ)*(major_s0_2) + (120773527/1000000000000 : ℝ)*(sp_s0_1) + (513247/500000000000 : ℝ)*(sp_s0_2) + (691214533767/200000000000 : ℝ)*(sp_s0_3) + (25014619/1000000000000 : ℝ)*(sp_s0_13) + (1544788277229/250000000000 : ℝ)*(sp_s0_14) + (617893232837/100000000000 : ℝ)*(sp_s0_15) + (6179152082423/1000000000000 : ℝ)*(sp_s0_16) + (2763634667047/1000000000000 : ℝ)*(sp_s0_19) + (100007019/1000000000000 : ℝ)*(sp_s0_21) + (1381829840833/500000000000 : ℝ)*(f.failure) + (1544788277229/250000000000 : ℝ)*(f.sum) + (342319491/2500000000000000000000 : ℝ)*base62 + (2118025933588539/5000000000000000000000000000 : ℝ)*base65 + (415685321088539/5000000000000000000000000000 : ℝ)*base67 + (3373007070279737/5000000000000000000000000000 : ℝ)*base69 + (593321053902087/1250000000000000000000000000 : ℝ)*base71 + (94507310422323/5000000000000000000000000000 : ℝ)*base73 + (589498143220263/5000000000000000000000000000 : ℝ)*base75 + (3118337060519809/5000000000000000000000000000 : ℝ)*base77 + (860921441494569/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (56431/50000000000000000 : ℝ)*base86 + (6431/50000000000000000 : ℝ)*base88 + (6431/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-3433/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-3433/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3249988120858597048593/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (799734811651/1000000000000 : ℝ)*(base1) + (266679175873/500000000000 : ℝ)*(base40) + (49159078473/200000000000 : ℝ)*(base50) + (135440174419/500000000000 : ℝ)*(base60) + (423971468327/62500000000 : ℝ)*(major_s0_0) + (2872375499891/1000000000000 : ℝ)*(major_s0_1) + (2872375499891/1000000000000 : ℝ)*(major_s0_2) + (26697321/1000000000000 : ℝ)*(sp_s0_1) + (3911167993341/1000000000000 : ℝ)*(sp_s0_3) + (194533803/1000000000000 : ℝ)*(sp_s0_15) + (4769142558817/1000000000000 : ℝ)*(sp_s0_20) + (1984593258021/500000000000 : ℝ)*(sp_s0_21) + (793881549433/200000000000 : ℝ)*(sp_s0_22) + (30487655447/31250000000 : ℝ)*(sp_s0_25) + (443834946489/250000000000 : ℝ)*(f.failure) + (793881549433/200000000000 : ℝ)*(f.sum) + (7021481949/10000000000000000000000 : ℝ)*base62 + (4739093244706531/10000000000000000000000000000 : ℝ)*base65 + (3178762256293469/10000000000000000000000000000 : ℝ)*base66 + (5384739059758927/10000000000000000000000000000 : ℝ)*base68 + (386684921922807/2000000000000000000000000000 : ℝ)*base71 + (122784425056593/625000000000000000000000000 : ℝ)*base73 + (1269549016241073/10000000000000000000000000000 : ℝ)*base74 + (87701780619219/625000000000000000000000000 : ℝ)*base77 + (5238545538387981/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (19777/25000000000000000 : ℝ)*base87 + (19777/25000000000000000 : ℝ)*base89 + (19777/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (5281/100000 : ℝ) ^ (35/8 : ℝ) ≤ (129078300034919/50000000000000000000 : ℝ) := by
    have hpowers : (5281/100000 : ℝ)^35 ≤ (129078300034919/50000000000000000000 : ℝ)^8 := by
      have hnat : (5281 : ℕ)^35*50000000000000000000^8 ≤ 129078300034919^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5281 100000 129078300034919 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5281/100000 : ℝ)) (X := (129078300034919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50000129078300034919/50000000000000000000 : ℝ) ≤ (2500001475179103/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50000129078300034919/50000000000000000000 : ℝ)^8 ≤ (2500001475179103/2500000000000000 : ℝ)^35 := by
      have hnat : (50000129078300034919 : ℕ)^8*2500000000000000^35 ≤ 2500001475179103^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000129078300034919 50000000000000000000 2500001475179103 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001475179103/2500000000000000 : ℝ)) (X := (50000129078300034919/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25000129078300034919/25000000000000000000 : ℝ) ≤ (10000011801421073/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25000129078300034919/25000000000000000000 : ℝ)^8 ≤ (10000011801421073/10000000000000000 : ℝ)^35 := by
      have hnat : (25000129078300034919 : ℕ)^8*10000000000000000^35 ≤ 10000011801421073^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000129078300034919 25000000000000000000 10000011801421073 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000011801421073/10000000000000000 : ℝ)) (X := (25000129078300034919/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1475179103/132025000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5900704661/528100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (5281/100000 : ℝ)) (alpha := (1475179103/132025000000000 : ℝ)) (beta := (5900704661/528100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5281/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1475179103/132025000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5900704661/528100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (23207/100000 : ℝ) ^ (35/8 : ℝ) ≤ (167719336192386519/100000000000000000000 : ℝ) := by
    have hpowers : (23207/100000 : ℝ)^35 ≤ (167719336192386519/100000000000000000000 : ℝ)^8 := by
      have hnat : (23207 : ℕ)^35*100000000000000000000^8 ≤ 167719336192386519^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23207 100000 167719336192386519 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23207/100000 : ℝ)) (X := (167719336192386519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100167719336192386519/100000000000000000000 : ℝ) ≤ (5001915553633793/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100167719336192386519/100000000000000000000 : ℝ)^8 ≤ (5001915553633793/5000000000000000 : ℝ)^35 := by
      have hnat : (100167719336192386519 : ℕ)^8*5000000000000000^35 ≤ 5001915553633793^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100167719336192386519 100000000000000000000 5001915553633793 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001915553633793/5000000000000000 : ℝ)) (X := (100167719336192386519/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50167719336192386519/50000000000000000000 : ℝ) ≤ (5003828634602969/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50167719336192386519/50000000000000000000 : ℝ)^8 ≤ (5003828634602969/5000000000000000 : ℝ)^35 := by
      have hnat : (50167719336192386519 : ℕ)^8*5000000000000000^35 ≤ 5003828634602969^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50167719336192386519 50000000000000000000 5003828634602969 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003828634602969/5000000000000000 : ℝ)) (X := (50167719336192386519/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1915553633793/1160350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(239135121147/145043750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (23207/100000 : ℝ)) (alpha := (1915553633793/1160350000000000 : ℝ)) (beta := (239135121147/145043750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (23207/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1915553633793/1160350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(239135121147/145043750000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3433/20000 : ℝ) ^ (35/8 : ℝ) ≤ (44829785302234737/100000000000000000000 : ℝ) := by
    have hpowers : (3433/20000 : ℝ)^35 ≤ (44829785302234737/100000000000000000000 : ℝ)^8 := by
      have hnat : (3433 : ℕ)^35*100000000000000000000^8 ≤ 44829785302234737^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3433 20000 44829785302234737 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3433/20000 : ℝ)) (X := (44829785302234737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100044829785302234737/100000000000000000000 : ℝ) ≤ (10001024503671231/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100044829785302234737/100000000000000000000 : ℝ)^8 ≤ (10001024503671231/10000000000000000 : ℝ)^35 := by
      have hnat : (100044829785302234737 : ℕ)^8*10000000000000000^35 ≤ 10001024503671231^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044829785302234737 100000000000000000000 10001024503671231 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001024503671231/10000000000000000 : ℝ)) (X := (100044829785302234737/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50044829785302234737/50000000000000000000 : ℝ) ≤ (10002048653258539/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50044829785302234737/50000000000000000000 : ℝ)^8 ≤ (10002048653258539/10000000000000000 : ℝ)^35 := by
      have hnat : (50044829785302234737 : ℕ)^8*10000000000000000^35 ≤ 10002048653258539^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044829785302234737 50000000000000000000 10002048653258539 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002048653258539/10000000000000000 : ℝ)) (X := (50044829785302234737/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1024503671231/1716500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(256037396827/429125000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (3433/20000 : ℝ)) (alpha := (1024503671231/1716500000000000 : ℝ)) (beta := (256037396827/429125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (3433/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1024503671231/1716500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(256037396827/429125000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3364360023/10000000000 : ℝ)*X 0 0+(-417990509/1000000000 : ℝ)*X 0 1+(-2583033329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1931455303/5000000000 : ℝ)*X 1 0+(964638663/2000000000 : ℝ)*X 1 1+(-4062019709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5415621163/10000000000 : ℝ)*X 2 0+(-3948051657/10000000000 : ℝ)*X 2 1+(3324988777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4411178997/10000000000 : ℝ)*X 0 0+(-3729767427/10000000000 : ℝ)*X 0 1+(-4609728387/10000000000 : ℝ)*X 0 2+(4411178997/10000000000 : ℝ)*X 1 0+(-3729767427/10000000000 : ℝ)*X 1 1+(-4609728387/10000000000 : ℝ)*X 1 2+(4411178997/10000000000 : ℝ)*X 2 0+(-3729767427/10000000000 : ℝ)*X 2 1+(-4609728387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310032_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-601141237141801258777525667949/90648365000000000000000000000 : ℝ) := by norm_num
    linear_combination (522653/500000000000 : ℝ)*(base5) + (74527/125000000000 : ℝ)*(base17) + (631737/1000000000000 : ℝ)*(base21) + (63122948419/100000000000 : ℝ)*(base39) + (46526124837/125000000000 : ℝ)*(base40) + (4413389891/250000000000 : ℝ)*(base50) + (8371/15625000000 : ℝ)*(base59) + (160970674489/500000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (1105262143339/500000000000 : ℝ)*(sp_s1_0) + (1105261845231/500000000000 : ℝ)*(sp_s1_1) + (1105262350123/500000000000 : ℝ)*(sp_s1_2) + (499999477347/500000000000 : ℝ)*(sp_s1_6) + (1105262143339/500000000000 : ℝ)*(f.sum) + (81293469473322111/199174077500000000000000000000 : ℝ)*base62 + (2451638525993/17165000000000000000000000 : ℝ)*base64 + (53684853574343/116035000000000000000000000 : ℝ)*base66 + (604491368837/3433000000000000000000000 : ℝ)*base68 + (13935257030606777/22662091250000000000000000000 : ℝ)*base70 + (3975950706527/6601250000000000000000000 : ℝ)*base73 + (4507256634543/14504375000000000000000000 : ℝ)*base75 + (1043427721281/1320250000000000000000000 : ℝ)*base76 + (134501807024960453/306390417500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c310033_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-25491239/78125000 : ℝ)*x 0 + (-132113453/250000000 : ℝ)*x 1 + (4148563769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25491239/78125000 : ℝ)^9 ≤ (23693528796059/100000000000000 : ℝ)^7 := by
    have hnat : (25491239 : ℕ)^9*100000000000000^7 ≤ 23693528796059^7*78125000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25491239 78125000 23693528796059 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132113453/250000000 : ℝ)^9 ≤ (176167657361/400000000000 : ℝ)^7 := by
    have hnat : (132113453 : ℕ)^9*400000000000^7 ≤ 176167657361^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132113453 250000000 176167657361 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148563769/10000000000 : ℝ)^9 ≤ (16132278425121/50000000000000 : ℝ)^7 := by
    have hnat : (4148563769 : ℕ)^9*50000000000000^7 ≤ 16132278425121^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148563769 10000000000 16132278425121 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25491239/78125000 : ℝ), (-132113453/250000000 : ℝ), (4148563769/10000000000 : ℝ)] ![(23693528796059/100000000000000 : ℝ), (176167657361/400000000000 : ℝ), (16132278425121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25491239/78125000 : ℝ)|^9 ≤ (23693528796059/100000000000000 : ℝ)^7
        have hw : |(-25491239/78125000 : ℝ)|=(25491239/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132113453/250000000 : ℝ)|^9 ≤ (176167657361/400000000000 : ℝ)^7
        have hw : |(-132113453/250000000 : ℝ)|=(132113453/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148563769/10000000000 : ℝ)|^9 ≤ (16132278425121/50000000000000 : ℝ)^7
        have hw : |(4148563769/10000000000 : ℝ)|=(4148563769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310033_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1379584013/5000000000 : ℝ)*x 0 + (14465081/31250000 : ℝ)*x 1 + (1051590361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379584013/5000000000 : ℝ)^9 ≤ (19098553555807/100000000000000 : ℝ)^7 := by
    have hnat : (1379584013 : ℕ)^9*100000000000000^7 ≤ 19098553555807^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379584013 5000000000 19098553555807 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14465081/31250000 : ℝ)^9 ≤ (4643025871183/12500000000000 : ℝ)^7 := by
    have hnat : (14465081 : ℕ)^9*12500000000000^7 ≤ 4643025871183^7*31250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14465081 31250000 4643025871183 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051590361/2000000000 : ℝ)^9 ≤ (43757239457913/100000000000000 : ℝ)^7 := by
    have hnat : (1051590361 : ℕ)^9*100000000000000^7 ≤ 43757239457913^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051590361 2000000000 43757239457913 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379584013/5000000000 : ℝ), (14465081/31250000 : ℝ), (1051590361/2000000000 : ℝ)] ![(19098553555807/100000000000000 : ℝ), (4643025871183/12500000000000 : ℝ), (43757239457913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379584013/5000000000 : ℝ)|^9 ≤ (19098553555807/100000000000000 : ℝ)^7
        have hw : |(1379584013/5000000000 : ℝ)|=(1379584013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14465081/31250000 : ℝ)|^9 ≤ (4643025871183/12500000000000 : ℝ)^7
        have hw : |(14465081/31250000 : ℝ)|=(14465081/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051590361/2000000000 : ℝ)|^9 ≤ (43757239457913/100000000000000 : ℝ)^7
        have hw : |(1051590361/2000000000 : ℝ)|=(1051590361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310033_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6170081997/10000000000 : ℝ)*x 0 + (-2987777959/10000000000 : ℝ)*x 1 + (-3411903867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6170081997/10000000000 : ℝ)^9 ≤ (53749454386687/100000000000000 : ℝ)^7 := by
    have hnat : (6170081997 : ℕ)^9*100000000000000^7 ≤ 53749454386687^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6170081997 10000000000 53749454386687 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987777959/10000000000 : ℝ)^9 ≤ (10578347832929/50000000000000 : ℝ)^7 := by
    have hnat : (2987777959 : ℕ)^9*50000000000000^7 ≤ 10578347832929^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987777959 10000000000 10578347832929 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3411903867/10000000000 : ℝ)^9 ≤ (25093849928163/100000000000000 : ℝ)^7 := by
    have hnat : (3411903867 : ℕ)^9*100000000000000^7 ≤ 25093849928163^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411903867 10000000000 25093849928163 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6170081997/10000000000 : ℝ), (-2987777959/10000000000 : ℝ), (-3411903867/10000000000 : ℝ)] ![(53749454386687/100000000000000 : ℝ), (10578347832929/50000000000000 : ℝ), (25093849928163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6170081997/10000000000 : ℝ)|^9 ≤ (53749454386687/100000000000000 : ℝ)^7
        have hw : |(6170081997/10000000000 : ℝ)|=(6170081997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2987777959/10000000000 : ℝ)|^9 ≤ (10578347832929/50000000000000 : ℝ)^7
        have hw : |(-2987777959/10000000000 : ℝ)|=(2987777959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3411903867/10000000000 : ℝ)|^9 ≤ (25093849928163/100000000000000 : ℝ)^7
        have hw : |(-3411903867/10000000000 : ℝ)|=(3411903867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310033_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1254217439/2500000000 : ℝ)*x 0 + (-3793753341/10000000000 : ℝ)*x 1 + (98119357/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1254217439/2500000000 : ℝ)^9 ≤ (41194781656933/100000000000000 : ℝ)^7 := by
    have hnat : (1254217439 : ℕ)^9*100000000000000^7 ≤ 41194781656933^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254217439 2500000000 41194781656933 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3793753341/10000000000 : ℝ)^9 ≤ (14380471349939/50000000000000 : ℝ)^7 := by
    have hnat : (3793753341 : ℕ)^9*50000000000000^7 ≤ 14380471349939^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3793753341 10000000000 14380471349939 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98119357/250000000 : ℝ)^9 ≤ (3004427563311/10000000000000 : ℝ)^7 := by
    have hnat : (98119357 : ℕ)^9*10000000000000^7 ≤ 3004427563311^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98119357 250000000 3004427563311 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1254217439/2500000000 : ℝ), (-3793753341/10000000000 : ℝ), (98119357/250000000 : ℝ)] ![(41194781656933/100000000000000 : ℝ), (14380471349939/50000000000000 : ℝ), (3004427563311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1254217439/2500000000 : ℝ)|^9 ≤ (41194781656933/100000000000000 : ℝ)^7
        have hw : |(1254217439/2500000000 : ℝ)|=(1254217439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3793753341/10000000000 : ℝ)|^9 ≤ (14380471349939/50000000000000 : ℝ)^7
        have hw : |(-3793753341/10000000000 : ℝ)|=(3793753341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98119357/250000000 : ℝ)|^9 ≤ (3004427563311/10000000000000 : ℝ)^7
        have hw : |(98119357/250000000 : ℝ)|=(98119357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310033 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-25491239/78125000 : ℝ)*X 0 0+(-132113453/250000000 : ℝ)*X 0 1+(4148563769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310033_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1379584013/5000000000 : ℝ)*X 1 0+(14465081/31250000 : ℝ)*X 1 1+(1051590361/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310033_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6170081997/10000000000 : ℝ)*X 2 0+(-2987777959/10000000000 : ℝ)*X 2 1+(-3411903867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310033_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1254217439/2500000000 : ℝ)*X 0 0+(-3793753341/10000000000 : ℝ)*X 0 1+(98119357/250000000 : ℝ)*X 0 2+(1254217439/2500000000 : ℝ)*X 1 0+(-3793753341/10000000000 : ℝ)*X 1 1+(98119357/250000000 : ℝ)*X 1 2+(1254217439/2500000000 : ℝ)*X 2 0+(-3793753341/10000000000 : ℝ)*X 2 1+(98119357/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310033_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-16690840868381587511986590309/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90537217667/500000000000 : ℝ)*(base5) + (719117/1000000000000 : ℝ)*(base10) + (13153/40000000000 : ℝ)*(base13) + (104573/1000000000000 : ℝ)*(base39) + (310478342217/1000000000000 : ℝ)*(base40) + (47298353247/250000000000 : ℝ)*(base49) + (121763/1000000000000 : ℝ)*(base53) + (315291180821/1000000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s0_0) + (161793/100000 : ℝ)*(major_s0_1) + (1617929878237/1000000000000 : ℝ)*(major_s0_2) + (445088855881/200000000000 : ℝ)*(sp_s0_0) + (2225445327347/1000000000000 : ℝ)*(sp_s0_1) + (601629971111/250000000000 : ℝ)*(sp_s0_2) + (409462782333/500000000000 : ℝ)*(sp_s0_6) + (2225445449109/1000000000000 : ℝ)*(f.sum) + (3016008137575489/10000000000000000000000000000 : ℝ)*base62 + (7221084503484717/10000000000000000000000000000 : ℝ)*base65 + (2138320559/2000000000000000000000 : ℝ)*base66 + (3735237129575489/10000000000000000000000000000 : ℝ)*base68 + (3221655873484717/10000000000000000000000000000 : ℝ)*base71 + (2273193389/2000000000000000000000 : ℝ)*base72 + (2094985977/5000000000000000000000 : ℝ)*base74 + (411455389/1250000000000000000000 : ℝ)*base77 + (2179211383/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b019 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 32 ≤ c.val) (hhi : c.val < 34)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=32 ∨ c=33 := by omega
  rcases hc with rfl|rfl
  · exact collision_c310032 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310033 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 32 ≤ c.val) (hhi : c.val < 34)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
