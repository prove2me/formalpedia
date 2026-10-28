-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:14:34.020427+00:00
-- url     : https://prove2.me/submissions/3b6c1283-8013-4de0-8ac4-817326e86118

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10080
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
theorem collision_support_c302079_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8167221407/10000000000 : ℝ)*x 0 + (-308286393/2000000000 : ℝ)*x 1 + (-1196861967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8167221407/10000000000 : ℝ)^131 ≤ (76498674519463/100000000000000 : ℝ)^99 := by
    have hnat : (8167221407 : ℕ)^131*100000000000000^99 ≤ 76498674519463^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8167221407 10000000000 76498674519463 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308286393/2000000000 : ℝ)^131 ≤ (2105597100893/25000000000000 : ℝ)^99 := by
    have hnat : (308286393 : ℕ)^131*25000000000000^99 ≤ 2105597100893^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308286393 2000000000 2105597100893 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196861967/5000000000 : ℝ)^131 ≤ (471216783427/3125000000000 : ℝ)^99 := by
    have hnat : (1196861967 : ℕ)^131*3125000000000^99 ≤ 471216783427^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196861967 5000000000 471216783427 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8167221407/10000000000 : ℝ), (-308286393/2000000000 : ℝ), (-1196861967/5000000000 : ℝ)] ![(76498674519463/100000000000000 : ℝ), (2105597100893/25000000000000 : ℝ), (471216783427/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8167221407/10000000000 : ℝ)|^131 ≤ (76498674519463/100000000000000 : ℝ)^99
        have hw : |(8167221407/10000000000 : ℝ)|=(8167221407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308286393/2000000000 : ℝ)|^131 ≤ (2105597100893/25000000000000 : ℝ)^99
        have hw : |(-308286393/2000000000 : ℝ)|=(308286393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1196861967/5000000000 : ℝ)|^131 ≤ (471216783427/3125000000000 : ℝ)^99
        have hw : |(-1196861967/5000000000 : ℝ)|=(1196861967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (653812867/2000000000 : ℝ)*x 0 + (3035706847/5000000000 : ℝ)*x 1 + (1783083217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653812867/2000000000 : ℝ)^131 ≤ (22775579548597/100000000000000 : ℝ)^99 := by
    have hnat : (653812867 : ℕ)^131*100000000000000^99 ≤ 22775579548597^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653812867 2000000000 22775579548597 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3035706847/5000000000 : ℝ)^131 ≤ (5167043202607/10000000000000 : ℝ)^99 := by
    have hnat : (3035706847 : ℕ)^131*10000000000000^99 ≤ 5167043202607^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035706847 5000000000 5167043202607 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783083217/5000000000 : ℝ)^131 ≤ (25553988402743/100000000000000 : ℝ)^99 := by
    have hnat : (1783083217 : ℕ)^131*100000000000000^99 ≤ 25553988402743^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783083217 5000000000 25553988402743 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653812867/2000000000 : ℝ), (3035706847/5000000000 : ℝ), (1783083217/5000000000 : ℝ)] ![(22775579548597/100000000000000 : ℝ), (5167043202607/10000000000000 : ℝ), (25553988402743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653812867/2000000000 : ℝ)|^131 ≤ (22775579548597/100000000000000 : ℝ)^99
        have hw : |(653812867/2000000000 : ℝ)|=(653812867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3035706847/5000000000 : ℝ)|^131 ≤ (5167043202607/10000000000000 : ℝ)^99
        have hw : |(3035706847/5000000000 : ℝ)|=(3035706847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1783083217/5000000000 : ℝ)|^131 ≤ (25553988402743/100000000000000 : ℝ)^99
        have hw : |(1783083217/5000000000 : ℝ)|=(1783083217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3502692539/10000000000 : ℝ)*x 0 + (5323140891/10000000000 : ℝ)*x 1 + (-4189928453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3502692539/10000000000 : ℝ)^131 ≤ (1559617286629/6250000000000 : ℝ)^99 := by
    have hnat : (3502692539 : ℕ)^131*6250000000000^99 ≤ 1559617286629^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3502692539 10000000000 1559617286629 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5323140891/10000000000 : ℝ)^131 ≤ (2713542402127/6250000000000 : ℝ)^99 := by
    have hnat : (5323140891 : ℕ)^131*6250000000000^99 ≤ 2713542402127^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323140891 10000000000 2713542402127 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4189928453/10000000000 : ℝ)^131 ≤ (31629444962731/100000000000000 : ℝ)^99 := by
    have hnat : (4189928453 : ℕ)^131*100000000000000^99 ≤ 31629444962731^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189928453 10000000000 31629444962731 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3502692539/10000000000 : ℝ), (5323140891/10000000000 : ℝ), (-4189928453/10000000000 : ℝ)] ![(1559617286629/6250000000000 : ℝ), (2713542402127/6250000000000 : ℝ), (31629444962731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3502692539/10000000000 : ℝ)|^131 ≤ (1559617286629/6250000000000 : ℝ)^99
        have hw : |(3502692539/10000000000 : ℝ)|=(3502692539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5323140891/10000000000 : ℝ)|^131 ≤ (2713542402127/6250000000000 : ℝ)^99
        have hw : |(5323140891/10000000000 : ℝ)|=(5323140891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4189928453/10000000000 : ℝ)|^131 ≤ (31629444962731/100000000000000 : ℝ)^99
        have hw : |(-4189928453/10000000000 : ℝ)|=(4189928453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-838511029/5000000000 : ℝ)*x 0 + (362508827/1250000000 : ℝ)*x 1 + (-7731551091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838511029/5000000000 : ℝ)^131 ≤ (4708197213279/50000000000000 : ℝ)^99 := by
    have hnat : (838511029 : ℕ)^131*50000000000000^99 ≤ 4708197213279^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838511029 5000000000 4708197213279 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362508827/1250000000 : ℝ)^131 ≤ (19437555530257/100000000000000 : ℝ)^99 := by
    have hnat : (362508827 : ℕ)^131*100000000000000^99 ≤ 19437555530257^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362508827 1250000000 19437555530257 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7731551091/10000000000 : ℝ)^131 ≤ (8893256252659/12500000000000 : ℝ)^99 := by
    have hnat : (7731551091 : ℕ)^131*12500000000000^99 ≤ 8893256252659^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7731551091 10000000000 8893256252659 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-838511029/5000000000 : ℝ), (362508827/1250000000 : ℝ), (-7731551091/10000000000 : ℝ)] ![(4708197213279/50000000000000 : ℝ), (19437555530257/100000000000000 : ℝ), (8893256252659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-838511029/5000000000 : ℝ)|^131 ≤ (4708197213279/50000000000000 : ℝ)^99
        have hw : |(-838511029/5000000000 : ℝ)|=(838511029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(362508827/1250000000 : ℝ)|^131 ≤ (19437555530257/100000000000000 : ℝ)^99
        have hw : |(362508827/1250000000 : ℝ)|=(362508827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7731551091/10000000000 : ℝ)|^131 ≤ (8893256252659/12500000000000 : ℝ)^99
        have hw : |(-7731551091/10000000000 : ℝ)|=(7731551091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1614439361/2000000000 : ℝ)*x 0 + (-272982577/10000000000 : ℝ)*x 1 + (-3382209651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614439361/2000000000 : ℝ)^131 ≤ (15064629738991/20000000000000 : ℝ)^99 := by
    have hnat : (1614439361 : ℕ)^131*20000000000000^99 ≤ 15064629738991^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614439361 2000000000 15064629738991 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272982577/10000000000 : ℝ)^131 ≤ (213099876437/25000000000000 : ℝ)^99 := by
    have hnat : (272982577 : ℕ)^131*25000000000000^99 ≤ 213099876437^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272982577 10000000000 213099876437 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3382209651/10000000000 : ℝ)^131 ≤ (23824451792719/100000000000000 : ℝ)^99 := by
    have hnat : (3382209651 : ℕ)^131*100000000000000^99 ≤ 23824451792719^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3382209651 10000000000 23824451792719 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1614439361/2000000000 : ℝ), (-272982577/10000000000 : ℝ), (-3382209651/10000000000 : ℝ)] ![(15064629738991/20000000000000 : ℝ), (213099876437/25000000000000 : ℝ), (23824451792719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1614439361/2000000000 : ℝ)|^131 ≤ (15064629738991/20000000000000 : ℝ)^99
        have hw : |(1614439361/2000000000 : ℝ)|=(1614439361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272982577/10000000000 : ℝ)|^131 ≤ (213099876437/25000000000000 : ℝ)^99
        have hw : |(-272982577/10000000000 : ℝ)|=(272982577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3382209651/10000000000 : ℝ)|^131 ≤ (23824451792719/100000000000000 : ℝ)^99
        have hw : |(-3382209651/10000000000 : ℝ)|=(3382209651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1405405077/10000000000 : ℝ)*x 0 + (8007088713/10000000000 : ℝ)*x 1 + (2739514029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405405077/10000000000 : ℝ)^131 ≤ (1490642222869/20000000000000 : ℝ)^99 := by
    have hnat : (1405405077 : ℕ)^131*20000000000000^99 ≤ 1490642222869^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405405077 10000000000 1490642222869 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8007088713/10000000000 : ℝ)^131 ≤ (37260143937241/50000000000000 : ℝ)^99 := by
    have hnat : (8007088713 : ℕ)^131*50000000000000^99 ≤ 37260143937241^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8007088713 10000000000 37260143937241 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739514029/10000000000 : ℝ)^131 ≤ (9013250501981/50000000000000 : ℝ)^99 := by
    have hnat : (2739514029 : ℕ)^131*50000000000000^99 ≤ 9013250501981^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739514029 10000000000 9013250501981 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1405405077/10000000000 : ℝ), (8007088713/10000000000 : ℝ), (2739514029/10000000000 : ℝ)] ![(1490642222869/20000000000000 : ℝ), (37260143937241/50000000000000 : ℝ), (9013250501981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1405405077/10000000000 : ℝ)|^131 ≤ (1490642222869/20000000000000 : ℝ)^99
        have hw : |(1405405077/10000000000 : ℝ)|=(1405405077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8007088713/10000000000 : ℝ)|^131 ≤ (37260143937241/50000000000000 : ℝ)^99
        have hw : |(8007088713/10000000000 : ℝ)|=(8007088713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739514029/10000000000 : ℝ)|^131 ≤ (9013250501981/50000000000000 : ℝ)^99
        have hw : |(2739514029/10000000000 : ℝ)|=(2739514029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (475774711/2000000000 : ℝ)*x 0 + (957413309/1250000000 : ℝ)*x 1 + (-2357414691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475774711/2000000000 : ℝ)^131 ≤ (14955275706147/100000000000000 : ℝ)^99 := by
    have hnat : (475774711 : ℕ)^131*100000000000000^99 ≤ 14955275706147^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475774711 2000000000 14955275706147 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957413309/1250000000 : ℝ)^131 ≤ (35133849583121/50000000000000 : ℝ)^99 := by
    have hnat : (957413309 : ℕ)^131*50000000000000^99 ≤ 35133849583121^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957413309 1250000000 35133849583121 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2357414691/10000000000 : ℝ)^131 ≤ (1477702511053/10000000000000 : ℝ)^99 := by
    have hnat : (2357414691 : ℕ)^131*10000000000000^99 ≤ 1477702511053^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357414691 10000000000 1477702511053 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(475774711/2000000000 : ℝ), (957413309/1250000000 : ℝ), (-2357414691/10000000000 : ℝ)] ![(14955275706147/100000000000000 : ℝ), (35133849583121/50000000000000 : ℝ), (1477702511053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(475774711/2000000000 : ℝ)|^131 ≤ (14955275706147/100000000000000 : ℝ)^99
        have hw : |(475774711/2000000000 : ℝ)|=(475774711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957413309/1250000000 : ℝ)|^131 ≤ (35133849583121/50000000000000 : ℝ)^99
        have hw : |(957413309/1250000000 : ℝ)|=(957413309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2357414691/10000000000 : ℝ)|^131 ≤ (1477702511053/10000000000000 : ℝ)^99
        have hw : |(-2357414691/10000000000 : ℝ)|=(2357414691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-287884449/10000000000 : ℝ)*x 0 + (3577128929/10000000000 : ℝ)*x 1 + (-7918193351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287884449/10000000000 : ℝ)^131 ≤ (914508458543/100000000000000 : ℝ)^99 := by
    have hnat : (287884449 : ℕ)^131*100000000000000^99 ≤ 914508458543^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287884449 10000000000 914508458543 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3577128929/10000000000 : ℝ)^131 ≤ (25657984766587/100000000000000 : ℝ)^99 := by
    have hnat : (3577128929 : ℕ)^131*100000000000000^99 ≤ 25657984766587^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577128929 10000000000 25657984766587 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7918193351/10000000000 : ℝ)^131 ≤ (73427506764299/100000000000000 : ℝ)^99 := by
    have hnat : (7918193351 : ℕ)^131*100000000000000^99 ≤ 73427506764299^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7918193351 10000000000 73427506764299 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287884449/10000000000 : ℝ), (3577128929/10000000000 : ℝ), (-7918193351/10000000000 : ℝ)] ![(914508458543/100000000000000 : ℝ), (25657984766587/100000000000000 : ℝ), (73427506764299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287884449/10000000000 : ℝ)|^131 ≤ (914508458543/100000000000000 : ℝ)^99
        have hw : |(-287884449/10000000000 : ℝ)|=(287884449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3577128929/10000000000 : ℝ)|^131 ≤ (25657984766587/100000000000000 : ℝ)^99
        have hw : |(3577128929/10000000000 : ℝ)|=(3577128929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7918193351/10000000000 : ℝ)|^131 ≤ (73427506764299/100000000000000 : ℝ)^99
        have hw : |(-7918193351/10000000000 : ℝ)|=(7918193351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4687897443/5000000000 : ℝ)*x 0 + (-1114882287/10000000000 : ℝ)*x 1 + (-650444777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4687897443/5000000000 : ℝ)^131 ≤ (45912423155117/50000000000000 : ℝ)^99 := by
    have hnat : (4687897443 : ℕ)^131*50000000000000^99 ≤ 45912423155117^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687897443 5000000000 45912423155117 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114882287/10000000000 : ℝ)^131 ≤ (5486086320791/100000000000000 : ℝ)^99 := by
    have hnat : (1114882287 : ℕ)^131*100000000000000^99 ≤ 5486086320791^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114882287 10000000000 5486086320791 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650444777/10000000000 : ℝ)^131 ≤ (1344533679311/50000000000000 : ℝ)^99 := by
    have hnat : (650444777 : ℕ)^131*50000000000000^99 ≤ 1344533679311^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650444777 10000000000 1344533679311 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4687897443/5000000000 : ℝ), (-1114882287/10000000000 : ℝ), (-650444777/10000000000 : ℝ)] ![(45912423155117/50000000000000 : ℝ), (5486086320791/100000000000000 : ℝ), (1344533679311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4687897443/5000000000 : ℝ)|^131 ≤ (45912423155117/50000000000000 : ℝ)^99
        have hw : |(4687897443/5000000000 : ℝ)|=(4687897443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114882287/10000000000 : ℝ)|^131 ≤ (5486086320791/100000000000000 : ℝ)^99
        have hw : |(-1114882287/10000000000 : ℝ)|=(1114882287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-650444777/10000000000 : ℝ)|^131 ≤ (1344533679311/50000000000000 : ℝ)^99
        have hw : |(-650444777/10000000000 : ℝ)|=(650444777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (250952037/625000000 : ℝ)*x 0 + (585870173/1000000000 : ℝ)*x 1 + (190879943/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250952037/625000000 : ℝ)^131 ≤ (29896283235263/100000000000000 : ℝ)^99 := by
    have hnat : (250952037 : ℕ)^131*100000000000000^99 ≤ 29896283235263^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250952037 625000000 29896283235263 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585870173/1000000000 : ℝ)^131 ≤ (9857738365671/20000000000000 : ℝ)^99 := by
    have hnat : (585870173 : ℕ)^131*20000000000000^99 ≤ 9857738365671^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585870173 1000000000 9857738365671 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190879943/625000000 : ℝ)^131 ≤ (5203756230747/25000000000000 : ℝ)^99 := by
    have hnat : (190879943 : ℕ)^131*25000000000000^99 ≤ 5203756230747^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190879943 625000000 5203756230747 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(250952037/625000000 : ℝ), (585870173/1000000000 : ℝ), (190879943/625000000 : ℝ)] ![(29896283235263/100000000000000 : ℝ), (9857738365671/20000000000000 : ℝ), (5203756230747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(250952037/625000000 : ℝ)|^131 ≤ (29896283235263/100000000000000 : ℝ)^99
        have hw : |(250952037/625000000 : ℝ)|=(250952037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585870173/1000000000 : ℝ)|^131 ≤ (9857738365671/20000000000000 : ℝ)^99
        have hw : |(585870173/1000000000 : ℝ)|=(585870173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190879943/625000000 : ℝ)|^131 ≤ (5203756230747/25000000000000 : ℝ)^99
        have hw : |(190879943/625000000 : ℝ)|=(190879943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2703244457/10000000000 : ℝ)*x 0 + (3236332591/10000000000 : ℝ)*x 1 + (-678150333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703244457/10000000000 : ℝ)^131 ≤ (8855687810691/50000000000000 : ℝ)^99 := by
    have hnat : (2703244457 : ℕ)^131*50000000000000^99 ≤ 8855687810691^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703244457 10000000000 8855687810691 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3236332591/10000000000 : ℝ)^131 ≤ (22474316214747/100000000000000 : ℝ)^99 := by
    have hnat : (3236332591 : ℕ)^131*100000000000000^99 ≤ 22474316214747^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3236332591 10000000000 22474316214747 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678150333/1000000000 : ℝ)^131 ≤ (116824820607/195312500000 : ℝ)^99 := by
    have hnat : (678150333 : ℕ)^131*195312500000^99 ≤ 116824820607^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678150333 1000000000 116824820607 195312500000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703244457/10000000000 : ℝ), (3236332591/10000000000 : ℝ), (-678150333/1000000000 : ℝ)] ![(8855687810691/50000000000000 : ℝ), (22474316214747/100000000000000 : ℝ), (116824820607/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703244457/10000000000 : ℝ)|^131 ≤ (8855687810691/50000000000000 : ℝ)^99
        have hw : |(2703244457/10000000000 : ℝ)|=(2703244457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3236332591/10000000000 : ℝ)|^131 ≤ (22474316214747/100000000000000 : ℝ)^99
        have hw : |(3236332591/10000000000 : ℝ)|=(3236332591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-678150333/1000000000 : ℝ)|^131 ≤ (116824820607/195312500000 : ℝ)^99
        have hw : |(-678150333/1000000000 : ℝ)|=(678150333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-219347637/5000000000 : ℝ)*x 0 + (90490571/156250000 : ℝ)*x 1 + (-5910156783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219347637/5000000000 : ℝ)^131 ≤ (1596857393691/100000000000000 : ℝ)^99 := by
    have hnat : (219347637 : ℕ)^131*100000000000000^99 ≤ 1596857393691^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219347637 5000000000 1596857393691 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90490571/156250000 : ℝ)^131 ≤ (48540830040209/100000000000000 : ℝ)^99 := by
    have hnat : (90490571 : ℕ)^131*100000000000000^99 ≤ 48540830040209^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90490571 156250000 48540830040209 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5910156783/10000000000 : ℝ)^131 ≤ (49862312546667/100000000000000 : ℝ)^99 := by
    have hnat : (5910156783 : ℕ)^131*100000000000000^99 ≤ 49862312546667^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910156783 10000000000 49862312546667 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219347637/5000000000 : ℝ), (90490571/156250000 : ℝ), (-5910156783/10000000000 : ℝ)] ![(1596857393691/100000000000000 : ℝ), (48540830040209/100000000000000 : ℝ), (49862312546667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219347637/5000000000 : ℝ)|^131 ≤ (1596857393691/100000000000000 : ℝ)^99
        have hw : |(-219347637/5000000000 : ℝ)|=(219347637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90490571/156250000 : ℝ)|^131 ≤ (48540830040209/100000000000000 : ℝ)^99
        have hw : |(90490571/156250000 : ℝ)|=(90490571/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5910156783/10000000000 : ℝ)|^131 ≤ (49862312546667/100000000000000 : ℝ)^99
        have hw : |(-5910156783/10000000000 : ℝ)|=(5910156783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2418696643/2500000000 : ℝ)*x 0 + (-41291071/1250000000 : ℝ)*x 1 + (-738937967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2418696643/2500000000 : ℝ)^131 ≤ (47859728615027/50000000000000 : ℝ)^99 := by
    have hnat : (2418696643 : ℕ)^131*50000000000000^99 ≤ 47859728615027^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418696643 2500000000 47859728615027 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41291071/1250000000 : ℝ)^131 ≤ (548518976877/50000000000000 : ℝ)^99 := by
    have hnat : (41291071 : ℕ)^131*50000000000000^99 ≤ 548518976877^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41291071 1250000000 548518976877 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738937967/10000000000 : ℝ)^131 ≤ (1591752406311/50000000000000 : ℝ)^99 := by
    have hnat : (738937967 : ℕ)^131*50000000000000^99 ≤ 1591752406311^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738937967 10000000000 1591752406311 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2418696643/2500000000 : ℝ), (-41291071/1250000000 : ℝ), (-738937967/10000000000 : ℝ)] ![(47859728615027/50000000000000 : ℝ), (548518976877/50000000000000 : ℝ), (1591752406311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2418696643/2500000000 : ℝ)|^131 ≤ (47859728615027/50000000000000 : ℝ)^99
        have hw : |(2418696643/2500000000 : ℝ)|=(2418696643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41291071/1250000000 : ℝ)|^131 ≤ (548518976877/50000000000000 : ℝ)^99
        have hw : |(-41291071/1250000000 : ℝ)|=(41291071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-738937967/10000000000 : ℝ)|^131 ≤ (1591752406311/50000000000000 : ℝ)^99
        have hw : |(-738937967/10000000000 : ℝ)|=(738937967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1311419549/5000000000 : ℝ)*x 0 + (781795157/1250000000 : ℝ)*x 1 + (3948615933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311419549/5000000000 : ℝ)^131 ≤ (680706425383/4000000000000 : ℝ)^99 := by
    have hnat : (1311419549 : ℕ)^131*4000000000000^99 ≤ 680706425383^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311419549 5000000000 680706425383 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781795157/1250000000 : ℝ)^131 ≤ (26870312213031/50000000000000 : ℝ)^99 := by
    have hnat : (781795157 : ℕ)^131*50000000000000^99 ≤ 26870312213031^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781795157 1250000000 26870312213031 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3948615933/10000000000 : ℝ)^131 ≤ (3655214366581/12500000000000 : ℝ)^99 := by
    have hnat : (3948615933 : ℕ)^131*12500000000000^99 ≤ 3655214366581^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948615933 10000000000 3655214366581 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311419549/5000000000 : ℝ), (781795157/1250000000 : ℝ), (3948615933/10000000000 : ℝ)] ![(680706425383/4000000000000 : ℝ), (26870312213031/50000000000000 : ℝ), (3655214366581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311419549/5000000000 : ℝ)|^131 ≤ (680706425383/4000000000000 : ℝ)^99
        have hw : |(1311419549/5000000000 : ℝ)|=(1311419549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781795157/1250000000 : ℝ)|^131 ≤ (26870312213031/50000000000000 : ℝ)^99
        have hw : |(781795157/1250000000 : ℝ)|=(781795157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3948615933/10000000000 : ℝ)|^131 ≤ (3655214366581/12500000000000 : ℝ)^99
        have hw : |(3948615933/10000000000 : ℝ)|=(3948615933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s0_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (914556267/2000000000 : ℝ)*x 0 + (5287270847/10000000000 : ℝ)*x 1 + (-1562715169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914556267/2000000000 : ℝ)^131 ≤ (8877277080629/25000000000000 : ℝ)^99 := by
    have hnat : (914556267 : ℕ)^131*25000000000000^99 ≤ 8877277080629^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914556267 2000000000 8877277080629 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5287270847/10000000000 : ℝ)^131 ≤ (21514985422349/50000000000000 : ℝ)^99 := by
    have hnat : (5287270847 : ℕ)^131*50000000000000^99 ≤ 21514985422349^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287270847 10000000000 21514985422349 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1562715169/5000000000 : ℝ)^131 ≤ (21460920821141/100000000000000 : ℝ)^99 := by
    have hnat : (1562715169 : ℕ)^131*100000000000000^99 ≤ 21460920821141^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562715169 5000000000 21460920821141 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(914556267/2000000000 : ℝ), (5287270847/10000000000 : ℝ), (-1562715169/5000000000 : ℝ)] ![(8877277080629/25000000000000 : ℝ), (21514985422349/50000000000000 : ℝ), (21460920821141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(914556267/2000000000 : ℝ)|^131 ≤ (8877277080629/25000000000000 : ℝ)^99
        have hw : |(914556267/2000000000 : ℝ)|=(914556267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5287270847/10000000000 : ℝ)|^131 ≤ (21514985422349/50000000000000 : ℝ)^99
        have hw : |(5287270847/10000000000 : ℝ)|=(5287270847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1562715169/5000000000 : ℝ)|^131 ≤ (21460920821141/100000000000000 : ℝ)^99
        have hw : |(-1562715169/5000000000 : ℝ)|=(1562715169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2677656967/10000000000 : ℝ)*x 0 + (2245392609/5000000000 : ℝ)*x 1 + (-1145638599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677656967/10000000000 : ℝ)^131 ≤ (3497976070711/20000000000000 : ℝ)^99 := by
    have hnat : (2677656967 : ℕ)^131*20000000000000^99 ≤ 3497976070711^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677656967 10000000000 3497976070711 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245392609/5000000000 : ℝ)^131 ≤ (17334511724719/50000000000000 : ℝ)^99 := by
    have hnat : (2245392609 : ℕ)^131*50000000000000^99 ≤ 17334511724719^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245392609 5000000000 17334511724719 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145638599/2000000000 : ℝ)^131 ≤ (9568219235749/20000000000000 : ℝ)^99 := by
    have hnat : (1145638599 : ℕ)^131*20000000000000^99 ≤ 9568219235749^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145638599 2000000000 9568219235749 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2677656967/10000000000 : ℝ), (2245392609/5000000000 : ℝ), (-1145638599/2000000000 : ℝ)] ![(3497976070711/20000000000000 : ℝ), (17334511724719/50000000000000 : ℝ), (9568219235749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2677656967/10000000000 : ℝ)|^131 ≤ (3497976070711/20000000000000 : ℝ)^99
        have hw : |(-2677656967/10000000000 : ℝ)|=(2677656967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245392609/5000000000 : ℝ)|^131 ≤ (17334511724719/50000000000000 : ℝ)^99
        have hw : |(2245392609/5000000000 : ℝ)|=(2245392609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1145638599/2000000000 : ℝ)|^131 ≤ (9568219235749/20000000000000 : ℝ)^99
        have hw : |(-1145638599/2000000000 : ℝ)|=(1145638599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3272337257/5000000000 : ℝ)*x 0 + (-290021617/1000000000 : ℝ)*x 1 + (-334682511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3272337257/5000000000 : ℝ)^131 ≤ (3566622438943/6250000000000 : ℝ)^99 := by
    have hnat : (3272337257 : ℕ)^131*6250000000000^99 ≤ 3566622438943^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3272337257 5000000000 3566622438943 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290021617/1000000000 : ℝ)^131 ≤ (3887769288573/20000000000000 : ℝ)^99 := by
    have hnat : (290021617 : ℕ)^131*20000000000000^99 ≤ 3887769288573^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290021617 1000000000 3887769288573 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334682511/1000000000 : ℝ)^131 ≤ (11747597258883/50000000000000 : ℝ)^99 := by
    have hnat : (334682511 : ℕ)^131*50000000000000^99 ≤ 11747597258883^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334682511 1000000000 11747597258883 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3272337257/5000000000 : ℝ), (-290021617/1000000000 : ℝ), (-334682511/1000000000 : ℝ)] ![(3566622438943/6250000000000 : ℝ), (3887769288573/20000000000000 : ℝ), (11747597258883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3272337257/5000000000 : ℝ)|^131 ≤ (3566622438943/6250000000000 : ℝ)^99
        have hw : |(3272337257/5000000000 : ℝ)|=(3272337257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290021617/1000000000 : ℝ)|^131 ≤ (3887769288573/20000000000000 : ℝ)^99
        have hw : |(-290021617/1000000000 : ℝ)|=(290021617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334682511/1000000000 : ℝ)|^131 ≤ (11747597258883/50000000000000 : ℝ)^99
        have hw : |(-334682511/1000000000 : ℝ)|=(334682511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3934402701/10000000000 : ℝ)*x 0 + (5246805559/10000000000 : ℝ)*x 1 + (3852414557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3934402701/10000000000 : ℝ)^131 ≤ (2910251662229/10000000000000 : ℝ)^99 := by
    have hnat : (3934402701 : ℕ)^131*10000000000000^99 ≤ 2910251662229^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3934402701 10000000000 2910251662229 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246805559/10000000000 : ℝ)^131 ≤ (42594739880029/100000000000000 : ℝ)^99 := by
    have hnat : (5246805559 : ℕ)^131*100000000000000^99 ≤ 42594739880029^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246805559 10000000000 42594739880029 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3852414557/10000000000 : ℝ)^131 ≤ (28302743489013/100000000000000 : ℝ)^99 := by
    have hnat : (3852414557 : ℕ)^131*100000000000000^99 ≤ 28302743489013^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852414557 10000000000 28302743489013 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3934402701/10000000000 : ℝ), (5246805559/10000000000 : ℝ), (3852414557/10000000000 : ℝ)] ![(2910251662229/10000000000000 : ℝ), (42594739880029/100000000000000 : ℝ), (28302743489013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3934402701/10000000000 : ℝ)|^131 ≤ (2910251662229/10000000000000 : ℝ)^99
        have hw : |(3934402701/10000000000 : ℝ)|=(3934402701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246805559/10000000000 : ℝ)|^131 ≤ (42594739880029/100000000000000 : ℝ)^99
        have hw : |(5246805559/10000000000 : ℝ)|=(5246805559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3852414557/10000000000 : ℝ)|^131 ≤ (28302743489013/100000000000000 : ℝ)^99
        have hw : |(3852414557/10000000000 : ℝ)|=(3852414557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302079_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (482565439/1250000000 : ℝ)*x 0 + (610620797/1250000000 : ℝ)*x 1 + (-107830017/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482565439/1250000000 : ℝ)^131 ≤ (14190800599153/50000000000000 : ℝ)^99 := by
    have hnat : (482565439 : ℕ)^131*50000000000000^99 ≤ 14190800599153^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482565439 1250000000 14190800599153 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610620797/1250000000 : ℝ)^131 ≤ (38751773583293/100000000000000 : ℝ)^99 := by
    have hnat : (610620797 : ℕ)^131*100000000000000^99 ≤ 38751773583293^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610620797 1250000000 38751773583293 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107830017/250000000 : ℝ)^131 ≤ (65733250399/200000000000 : ℝ)^99 := by
    have hnat : (107830017 : ℕ)^131*200000000000^99 ≤ 65733250399^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107830017 250000000 65733250399 200000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482565439/1250000000 : ℝ), (610620797/1250000000 : ℝ), (-107830017/250000000 : ℝ)] ![(14190800599153/50000000000000 : ℝ), (38751773583293/100000000000000 : ℝ), (65733250399/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482565439/1250000000 : ℝ)|^131 ≤ (14190800599153/50000000000000 : ℝ)^99
        have hw : |(482565439/1250000000 : ℝ)|=(482565439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(610620797/1250000000 : ℝ)|^131 ≤ (38751773583293/100000000000000 : ℝ)^99
        have hw : |(610620797/1250000000 : ℝ)|=(610620797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107830017/250000000 : ℝ)|^131 ≤ (65733250399/200000000000 : ℝ)^99
        have hw : |(-107830017/250000000 : ℝ)|=(107830017/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302079 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((8167221407/10000000000 : ℝ)*X 1 0+(-308286393/2000000000 : ℝ)*X 1 1+(-1196861967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((653812867/2000000000 : ℝ)*X 2 0+(3035706847/5000000000 : ℝ)*X 2 1+(1783083217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3502692539/10000000000 : ℝ)*X 0 0+(5323140891/10000000000 : ℝ)*X 0 1+(-4189928453/10000000000 : ℝ)*X 0 2+(3502692539/10000000000 : ℝ)*X 1 0+(5323140891/10000000000 : ℝ)*X 1 1+(-4189928453/10000000000 : ℝ)*X 1 2+(3502692539/10000000000 : ℝ)*X 2 0+(5323140891/10000000000 : ℝ)*X 2 1+(-4189928453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-838511029/5000000000 : ℝ)*X 0 0+(362508827/1250000000 : ℝ)*X 0 1+(-7731551091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1614439361/2000000000 : ℝ)*X 1 0+(-272982577/10000000000 : ℝ)*X 1 1+(-3382209651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1405405077/10000000000 : ℝ)*X 2 0+(8007088713/10000000000 : ℝ)*X 2 1+(2739514029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((475774711/2000000000 : ℝ)*X 0 0+(957413309/1250000000 : ℝ)*X 0 1+(-2357414691/10000000000 : ℝ)*X 0 2+(475774711/2000000000 : ℝ)*X 1 0+(957413309/1250000000 : ℝ)*X 1 1+(-2357414691/10000000000 : ℝ)*X 1 2+(475774711/2000000000 : ℝ)*X 2 0+(957413309/1250000000 : ℝ)*X 2 1+(-2357414691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-287884449/10000000000 : ℝ)*X 0 0+(3577128929/10000000000 : ℝ)*X 0 1+(-7918193351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4687897443/5000000000 : ℝ)*X 1 0+(-1114882287/10000000000 : ℝ)*X 1 1+(-650444777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((250952037/625000000 : ℝ)*X 2 0+(585870173/1000000000 : ℝ)*X 2 1+(190879943/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2703244457/10000000000 : ℝ)*X 0 0+(3236332591/10000000000 : ℝ)*X 0 1+(-678150333/1000000000 : ℝ)*X 0 2+(2703244457/10000000000 : ℝ)*X 1 0+(3236332591/10000000000 : ℝ)*X 1 1+(-678150333/1000000000 : ℝ)*X 1 2+(2703244457/10000000000 : ℝ)*X 2 0+(3236332591/10000000000 : ℝ)*X 2 1+(-678150333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-219347637/5000000000 : ℝ)*X 0 0+(90490571/156250000 : ℝ)*X 0 1+(-5910156783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2418696643/2500000000 : ℝ)*X 1 0+(-41291071/1250000000 : ℝ)*X 1 1+(-738937967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1311419549/5000000000 : ℝ)*X 2 0+(781795157/1250000000 : ℝ)*X 2 1+(3948615933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((914556267/2000000000 : ℝ)*X 0 0+(5287270847/10000000000 : ℝ)*X 0 1+(-1562715169/5000000000 : ℝ)*X 0 2+(914556267/2000000000 : ℝ)*X 1 0+(5287270847/10000000000 : ℝ)*X 1 1+(-1562715169/5000000000 : ℝ)*X 1 2+(914556267/2000000000 : ℝ)*X 2 0+(5287270847/10000000000 : ℝ)*X 2 1+(-1562715169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22789/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22789/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (541455312416794575951/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21343424131/31250000000 : ℝ)*(base39) + (446974678877/500000000000 : ℝ)*(base49) + (9022219/1000000000000 : ℝ)*(base53) + (574966654453/1000000000000 : ℝ)*(base60) + (2550622924243/1000000000000 : ℝ)*(major_s0_0) + (2550622924243/1000000000000 : ℝ)*(major_s0_1) + (2550613902023/1000000000000 : ℝ)*(major_s0_2) + (37861627/1000000000000 : ℝ)*(sp_s0_1) + (672711/1000000000000 : ℝ)*(sp_s0_6) + (3391323157761/1000000000000 : ℝ)*(sp_s0_7) + (678263750983/200000000000 : ℝ)*(sp_s0_8) + (3391365638761/1000000000000 : ℝ)*(sp_s0_9) + (213734490913/125000000000 : ℝ)*(sp_s0_13) + (1672939/50000000000 : ℝ)*(sp_s0_14) + (341975320003/200000000000 : ℝ)*(f.failure) + (3391365638761/1000000000000 : ℝ)*(f.sum) + (2608078774255731/5000000000000000000000000000 : ℝ)*base62 + (9405120662598751/10000000000000000000000000000 : ℝ)*base65 + (2320001064412489/10000000000000000000000000000 : ℝ)*base66 + (5017380035044571/10000000000000000000000000000 : ℝ)*base68 + (161096257775281/250000000000000000000000000 : ℝ)*base71 + (4237412065466891/10000000000000000000000000000 : ℝ)*base73 + (1520483818533109/10000000000000000000000000000 : ℝ)*base75 + (5731367660412489/10000000000000000000000000000 : ℝ)*base77 + (272720264472799/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1249/2000000000000000 : ℝ)*base86 + (1249/2000000000000000 : ℝ)*base88 + (751/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((14787/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(14787/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1674924509435767025979/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (520255030007/500000000000 : ℝ)*(base39) + (2855559/1000000000000 : ℝ)*(base40) + (499142842279/1000000000000 : ℝ)*(base49) + (188090076647/250000000000 : ℝ)*(base60) + (3111426229429/1000000000000 : ℝ)*(major_s0_0) + (3111426229429/1000000000000 : ℝ)*(major_s0_1) + (3111426229429/1000000000000 : ℝ)*(major_s0_2) + (2656549/200000000000 : ℝ)*(sp_s0_1) + (22357571/1000000000000 : ℝ)*(sp_s0_7) + (258562634131/62500000000 : ℝ)*(sp_s0_14) + (4136947883457/1000000000000 : ℝ)*(sp_s0_15) + (1034256125917/250000000000 : ℝ)*(sp_s0_16) + (2085825721947/1000000000000 : ℝ)*(sp_s0_20) + (12667493/200000000000 : ℝ)*(sp_s0_22) + (2085825721947/1000000000000 : ℝ)*(f.failure) + (1034256125917/250000000000 : ℝ)*(f.sum) + (4334423517028503/5000000000000000000000000000 : ℝ)*base62 + (9381065371608573/10000000000000000000000000000 : ℝ)*base65 + (8767222324551567/10000000000000000000000000000 : ℝ)*base66 + (3426932615551567/10000000000000000000000000000 : ℝ)*base69 + (194792699358007/500000000000000000000000000 : ℝ)*base71 + (6367924947391427/10000000000000000000000000000 : ℝ)*base72 + (3977530203608573/10000000000000000000000000000 : ℝ)*base74 + (746246825448433/10000000000000000000000000000 : ℝ)*base76 + (2485449898471497/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (6601/10000000000000000 : ℝ)*base86 + (6601/10000000000000000 : ℝ)*base88 + (6601/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23433/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23433/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17203678072172959952781/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2266751/1000000000000 : ℝ)*(base11) + (926668142543/1000000000000 : ℝ)*(base39) + (270624699087/500000000000 : ℝ)*(base49) + (1412849/1000000000000 : ℝ)*(base50) + (1228835771749/500000000000 : ℝ)*(major_s0_0) + (1228835771749/500000000000 : ℝ)*(major_s0_1) + (1228835771749/500000000000 : ℝ)*(major_s0_2) + (16293149/200000000000 : ℝ)*(sp_s0_2) + (3695349/200000000000 : ℝ)*(sp_s0_9) + (195197/1000000000000 : ℝ)*(sp_s0_13) + (816943577187/250000000000 : ℝ)*(sp_s0_21) + (3267776575499/1000000000000 : ℝ)*(sp_s0_22) + (326767663301/100000000000 : ℝ)*(sp_s0_23) + (1647564022473/1000000000000 : ℝ)*(sp_s0_27) + (164756421767/100000000000 : ℝ)*(f.failure) + (3267776575499/1000000000000 : ℝ)*(f.sum) + (663781871375257/2500000000000000000000000000 : ℝ)*base63 + (462615716150413/5000000000000000000000000000 : ℝ)*base65 + (116188701099073/5000000000000000000000000000 : ℝ)*base67 + (153085467599073/5000000000000000000000000000 : ℝ)*base68 + (19764023522433/250000000000000000000000000 : ℝ)*base70 + (714526746650413/5000000000000000000000000000 : ℝ)*base73 + (333689334650413/5000000000000000000000000000 : ℝ)*base74 + (3496863053599073/5000000000000000000000000000 : ℝ)*base76 + (1295202396875257/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (339/1000000000000000 : ℝ)*base87 + (339/1000000000000000 : ℝ)*base89 + (339/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (22789/50000 : ℝ) ^ (65/16 : ℝ) ≤ (2054297154539787263/50000000000000000000 : ℝ) := by
    have hpowers : (22789/50000 : ℝ)^65 ≤ (2054297154539787263/50000000000000000000 : ℝ)^16 := by
      have hnat : (22789 : ℕ)^65*50000000000000000000^16 ≤ 2054297154539787263^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22789 50000 2054297154539787263 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22789/50000 : ℝ)) (X := (2054297154539787263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (52054297154539787263/50000000000000000000 : ℝ) ≤ (2524901255218169/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52054297154539787263/50000000000000000000 : ℝ)^16 ≤ (2524901255218169/2500000000000000 : ℝ)^65 := by
      have hnat : (52054297154539787263 : ℕ)^16*2500000000000000^65 ≤ 2524901255218169^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52054297154539787263 50000000000000000000 2524901255218169 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524901255218169/2500000000000000 : ℝ)) (X := (52054297154539787263/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (27054297154539787263/25000000000000000000 : ℝ) ≤ (10196289391861299/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (27054297154539787263/25000000000000000000 : ℝ)^16 ≤ (10196289391861299/10000000000000000 : ℝ)^65 := by
      have hnat : (27054297154539787263 : ℕ)^16*10000000000000000^65 ≤ 10196289391861299^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27054297154539787263 25000000000000000000 10196289391861299 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10196289391861299/10000000000000000 : ℝ)) (X := (27054297154539787263/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(24901255218169/1139450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(96684370988623/4557800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (22789/50000 : ℝ)) (alpha := (24901255218169/1139450000000000 : ℝ)) (beta := (96684370988623/4557800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22789/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(24901255218169/1139450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(96684370988623/4557800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14787/25000 : ℝ) ^ (65/16 : ℝ) ≤ (11844221233910090591/100000000000000000000 : ℝ) := by
    have hpowers : (14787/25000 : ℝ)^65 ≤ (11844221233910090591/100000000000000000000 : ℝ)^16 := by
      have hnat : (14787 : ℕ)^65*100000000000000000000^16 ≤ 11844221233910090591^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14787 25000 11844221233910090591 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14787/25000 : ℝ)) (X := (11844221233910090591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (111844221233910090591/100000000000000000000 : ℝ) ≤ (10279367958777441/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (111844221233910090591/100000000000000000000 : ℝ)^16 ≤ (10279367958777441/10000000000000000 : ℝ)^65 := by
      have hnat : (111844221233910090591 : ℕ)^16*10000000000000000^65 ≤ 10279367958777441^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111844221233910090591 100000000000000000000 10279367958777441 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10279367958777441/10000000000000000 : ℝ)) (X := (111844221233910090591/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (61844221233910090591/50000000000000000000 : ℝ) ≤ (2107449438174143/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (61844221233910090591/50000000000000000000 : ℝ)^16 ≤ (2107449438174143/2000000000000000 : ℝ)^65 := by
      have hnat : (61844221233910090591 : ℕ)^16*2000000000000000^65 ≤ 2107449438174143^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61844221233910090591 50000000000000000000 2107449438174143 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2107449438174143/2000000000000000 : ℝ)) (X := (61844221233910090591/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(279367958777441/5914800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(128939616046637/2957400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (14787/25000 : ℝ)) (alpha := (279367958777441/5914800000000000 : ℝ)) (beta := (128939616046637/2957400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (14787/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(279367958777441/5914800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(128939616046637/2957400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (23433/50000 : ℝ) ^ (65/16 : ℝ) ≤ (2300542046114352233/50000000000000000000 : ℝ) := by
    have hpowers : (23433/50000 : ℝ)^65 ≤ (2300542046114352233/50000000000000000000 : ℝ)^16 := by
      have hnat : (23433 : ℕ)^65*50000000000000000000^16 ≤ 2300542046114352233^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23433 50000 2300542046114352233 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23433/50000 : ℝ)) (X := (2300542046114352233/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (52300542046114352233/50000000000000000000 : ℝ) ≤ (1263918062192699/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52300542046114352233/50000000000000000000 : ℝ)^16 ≤ (1263918062192699/1250000000000000 : ℝ)^65 := by
      have hnat : (52300542046114352233 : ℕ)^16*1250000000000000^65 ≤ 1263918062192699^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52300542046114352233 50000000000000000000 1263918062192699 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263918062192699/1250000000000000 : ℝ)) (X := (52300542046114352233/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (27300542046114352233/25000000000000000000 : ℝ) ≤ (5109527916841377/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (27300542046114352233/25000000000000000000 : ℝ)^16 ≤ (5109527916841377/5000000000000000 : ℝ)^65 := by
      have hnat : (27300542046114352233 : ℕ)^16*5000000000000000^65 ≤ 5109527916841377^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27300542046114352233 25000000000000000000 5109527916841377 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5109527916841377/5000000000000000 : ℝ)) (X := (27300542046114352233/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4639354064233/195275000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(53855668070581/2343300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (23433/50000 : ℝ)) (alpha := (4639354064233/195275000000000 : ℝ)) (beta := (53855668070581/2343300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (23433/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4639354064233/195275000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(53855668070581/2343300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2677656967/10000000000 : ℝ)*X 0 0+(2245392609/5000000000 : ℝ)*X 0 1+(-1145638599/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3272337257/5000000000 : ℝ)*X 1 0+(-290021617/1000000000 : ℝ)*X 1 1+(-334682511/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3934402701/10000000000 : ℝ)*X 2 0+(5246805559/10000000000 : ℝ)*X 2 1+(3852414557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((482565439/1250000000 : ℝ)*X 0 0+(610620797/1250000000 : ℝ)*X 0 1+(-107830017/250000000 : ℝ)*X 0 2+(482565439/1250000000 : ℝ)*X 1 0+(610620797/1250000000 : ℝ)*X 1 1+(-107830017/250000000 : ℝ)*X 1 2+(482565439/1250000000 : ℝ)*X 2 0+(610620797/1250000000 : ℝ)*X 2 1+(-107830017/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-129907428137594415198043128612649153/21934651214775000000000000000000000 : ℝ) := by norm_num
    linear_combination (19983/125000000000 : ℝ)*(base5) + (28759/1000000000000 : ℝ)*(base18) + (1053/15625000000 : ℝ)*(base23) + (39869/1000000000000 : ℝ)*(base29) + (184010187061/500000000000 : ℝ)*(base39) + (6677/250000000000 : ℝ)*(base44) + (263897690377/1000000000000 : ℝ)*(base49) + (75467378731/500000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s1_0) + (372924993323/250000000000 : ℝ)*(major_s1_1) + (14917/10000 : ℝ)*(major_s1_2) + (493539601129/250000000000 : ℝ)*(sp_s1_0) + (1974158349049/1000000000000 : ℝ)*(sp_s1_1) + (1974158496987/1000000000000 : ℝ)*(sp_s1_2) + (999999773559/1000000000000 : ℝ)*(sp_s1_6) + (493539601129/250000000000 : ℝ)*(f.sum) + (245642226912653321/5775062850000000000000000000000 : ℝ)*base62 + (962780833907/7322812500000000000000000 : ℝ)*base65 + (492780081773357/1478700000000000000000000000 : ℝ)*base67 + (9196780146767/39055000000000000000000000 : ℝ)*base68 + (879858721422863501/2670073185000000000000000000000 : ℝ)*base71 + (16549816958239/22789000000000000000000000 : ℝ)*base73 + (1822528107947/92418750000000000000000000 : ℝ)*base74 + (155970690724487/227890000000000000000000000 : ℝ)*base77 + (19696778787729994703/33698094300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b034 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c302079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10080 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
