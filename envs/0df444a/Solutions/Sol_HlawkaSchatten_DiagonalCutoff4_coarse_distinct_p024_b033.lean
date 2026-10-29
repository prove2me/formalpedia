-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:57:12.899608+00:00
-- url     : https://prove2.me/submissions/f2567f21-e773-4bac-b5a6-bfc6e1aa6bb8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324061_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324062_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c324061 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c324061_s0 p hpa hpb X hX
  have h1 := collision_c324061_s1 p hpa hpb X hX h0
  exact collision_c324061_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c324062 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c324062_s0 p hpa hpb X hX
  have h1 := collision_c324062_s1 p hpa hpb X hX h0
  exact collision_c324062_s2 p hpa hpb X hX h1

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
theorem collision_support_c324060_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1267417919/10000000000 : ℝ)*x 0 + (2261817087/5000000000 : ℝ)*x 1 + (-1222178071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1267417919/10000000000 : ℝ)^85 ≤ (7850571183589/100000000000000 : ℝ)^69 := by
    have hnat : (1267417919 : ℕ)^85*100000000000000^69 ≤ 7850571183589^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267417919 10000000000 7850571183589 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261817087/5000000000 : ℝ)^85 ≤ (4704468092197/12500000000000 : ℝ)^69 := by
    have hnat : (2261817087 : ℕ)^85*12500000000000^69 ≤ 4704468092197^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261817087 5000000000 4704468092197 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222178071/2000000000 : ℝ)^85 ≤ (1362842101773/2500000000000 : ℝ)^69 := by
    have hnat : (1222178071 : ℕ)^85*2500000000000^69 ≤ 1362842101773^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222178071 2000000000 1362842101773 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1267417919/10000000000 : ℝ), (2261817087/5000000000 : ℝ), (-1222178071/2000000000 : ℝ)] ![(7850571183589/100000000000000 : ℝ), (4704468092197/12500000000000 : ℝ), (1362842101773/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1267417919/10000000000 : ℝ)|^85 ≤ (7850571183589/100000000000000 : ℝ)^69
        have hw : |(-1267417919/10000000000 : ℝ)|=(1267417919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261817087/5000000000 : ℝ)|^85 ≤ (4704468092197/12500000000000 : ℝ)^69
        have hw : |(2261817087/5000000000 : ℝ)|=(2261817087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1222178071/2000000000 : ℝ)|^85 ≤ (1362842101773/2500000000000 : ℝ)^69
        have hw : |(-1222178071/2000000000 : ℝ)|=(1222178071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (904726621/2000000000 : ℝ)*x 0 + (-633708499/5000000000 : ℝ)*x 1 + (-6110891991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904726621/2000000000 : ℝ)^85 ≤ (37635733781361/100000000000000 : ℝ)^69 := by
    have hnat : (904726621 : ℕ)^85*100000000000000^69 ≤ 37635733781361^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904726621 2000000000 37635733781361 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633708499/5000000000 : ℝ)^85 ≤ (7850564155927/100000000000000 : ℝ)^69 := by
    have hnat : (633708499 : ℕ)^85*100000000000000^69 ≤ 7850564155927^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633708499 5000000000 7850564155927 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6110891991/10000000000 : ℝ)^85 ≤ (1090274040989/2000000000000 : ℝ)^69 := by
    have hnat : (6110891991 : ℕ)^85*2000000000000^69 ≤ 1090274040989^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6110891991 10000000000 1090274040989 2000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904726621/2000000000 : ℝ), (-633708499/5000000000 : ℝ), (-6110891991/10000000000 : ℝ)] ![(37635733781361/100000000000000 : ℝ), (7850564155927/100000000000000 : ℝ), (1090274040989/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904726621/2000000000 : ℝ)|^85 ≤ (37635733781361/100000000000000 : ℝ)^69
        have hw : |(904726621/2000000000 : ℝ)|=(904726621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-633708499/5000000000 : ℝ)|^85 ≤ (7850564155927/100000000000000 : ℝ)^69
        have hw : |(-633708499/5000000000 : ℝ)|=(633708499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6110891991/10000000000 : ℝ)|^85 ≤ (1090274040989/2000000000000 : ℝ)^69
        have hw : |(-6110891991/10000000000 : ℝ)|=(6110891991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19043201/125000000 : ℝ)*x 0 + (1543500823/10000000000 : ℝ)*x 1 + (-4177705853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19043201/125000000 : ℝ)^85 ≤ (1230980693129/12500000000000 : ℝ)^69 := by
    have hnat : (19043201 : ℕ)^85*12500000000000^69 ≤ 1230980693129^69*125000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19043201 125000000 1230980693129 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543500823/10000000000 : ℝ)^85 ≤ (250192653381/2500000000000 : ℝ)^69 := by
    have hnat : (1543500823 : ℕ)^85*2500000000000^69 ≤ 250192653381^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543500823 10000000000 250192653381 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4177705853/5000000000 : ℝ)^85 ≤ (5009028018837/6250000000000 : ℝ)^69 := by
    have hnat : (4177705853 : ℕ)^85*6250000000000^69 ≤ 5009028018837^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177705853 5000000000 5009028018837 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19043201/125000000 : ℝ), (1543500823/10000000000 : ℝ), (-4177705853/5000000000 : ℝ)] ![(1230980693129/12500000000000 : ℝ), (250192653381/2500000000000 : ℝ), (5009028018837/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19043201/125000000 : ℝ)|^85 ≤ (1230980693129/12500000000000 : ℝ)^69
        have hw : |(-19043201/125000000 : ℝ)|=(19043201/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1543500823/10000000000 : ℝ)|^85 ≤ (250192653381/2500000000000 : ℝ)^69
        have hw : |(1543500823/10000000000 : ℝ)|=(1543500823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4177705853/5000000000 : ℝ)|^85 ≤ (5009028018837/6250000000000 : ℝ)^69
        have hw : |(-4177705853/5000000000 : ℝ)|=(4177705853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (298189513/1250000000 : ℝ)*x 0 + (-135037971/2500000000 : ℝ)*x 1 + (-8355412009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (298189513/1250000000 : ℝ)^85 ≤ (2138767794659/12500000000000 : ℝ)^69 := by
    have hnat : (298189513 : ℕ)^85*12500000000000^69 ≤ 2138767794659^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298189513 1250000000 2138767794659 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135037971/2500000000 : ℝ)^85 ≤ (1372702870699/50000000000000 : ℝ)^69 := by
    have hnat : (135037971 : ℕ)^85*50000000000000^69 ≤ 1372702870699^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135037971 2500000000 1372702870699 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8355412009/10000000000 : ℝ)^85 ≤ (80144451881681/100000000000000 : ℝ)^69 := by
    have hnat : (8355412009 : ℕ)^85*100000000000000^69 ≤ 80144451881681^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8355412009 10000000000 80144451881681 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(298189513/1250000000 : ℝ), (-135037971/2500000000 : ℝ), (-8355412009/10000000000 : ℝ)] ![(2138767794659/12500000000000 : ℝ), (1372702870699/50000000000000 : ℝ), (80144451881681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(298189513/1250000000 : ℝ)|^85 ≤ (2138767794659/12500000000000 : ℝ)^69
        have hw : |(298189513/1250000000 : ℝ)|=(298189513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135037971/2500000000 : ℝ)|^85 ≤ (1372702870699/50000000000000 : ℝ)^69
        have hw : |(-135037971/2500000000 : ℝ)|=(135037971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8355412009/10000000000 : ℝ)|^85 ≤ (80144451881681/100000000000000 : ℝ)^69
        have hw : |(-8355412009/10000000000 : ℝ)|=(8355412009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1013649369/5000000000 : ℝ)*x 0 + (2018986859/2500000000 : ℝ)*x 1 + (1434252213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013649369/5000000000 : ℝ)^85 ≤ (7001208795809/50000000000000 : ℝ)^69 := by
    have hnat : (1013649369 : ℕ)^85*50000000000000^69 ≤ 7001208795809^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013649369 5000000000 7001208795809 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018986859/2500000000 : ℝ)^85 ≤ (1921379446477/2500000000000 : ℝ)^69 := by
    have hnat : (2018986859 : ℕ)^85*2500000000000^69 ≤ 1921379446477^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018986859 2500000000 1921379446477 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1434252213/10000000000 : ℝ)^85 ≤ (2285601132283/25000000000000 : ℝ)^69 := by
    have hnat : (1434252213 : ℕ)^85*25000000000000^69 ≤ 2285601132283^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434252213 10000000000 2285601132283 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013649369/5000000000 : ℝ), (2018986859/2500000000 : ℝ), (1434252213/10000000000 : ℝ)] ![(7001208795809/50000000000000 : ℝ), (1921379446477/2500000000000 : ℝ), (2285601132283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013649369/5000000000 : ℝ)|^85 ≤ (7001208795809/50000000000000 : ℝ)^69
        have hw : |(1013649369/5000000000 : ℝ)|=(1013649369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018986859/2500000000 : ℝ)|^85 ≤ (1921379446477/2500000000000 : ℝ)^69
        have hw : |(2018986859/2500000000 : ℝ)|=(2018986859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1434252213/10000000000 : ℝ)|^85 ≤ (2285601132283/25000000000000 : ℝ)^69
        have hw : |(1434252213/10000000000 : ℝ)|=(1434252213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (852677999/2000000000 : ℝ)*x 0 + (3525000289/5000000000 : ℝ)*x 1 + (-912077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852677999/2000000000 : ℝ)^85 ≤ (4373319191543/12500000000000 : ℝ)^69 := by
    have hnat : (852677999 : ℕ)^85*12500000000000^69 ≤ 4373319191543^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852677999 2000000000 4373319191543 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3525000289/5000000000 : ℝ)^85 ≤ (4063185543169/6250000000000 : ℝ)^69 := by
    have hnat : (3525000289 : ℕ)^85*6250000000000^69 ≤ 4063185543169^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3525000289 5000000000 4063185543169 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912077/5000000000 : ℝ)^85 ≤ (38715181/1562500000000 : ℝ)^69 := by
    have hnat : (912077 : ℕ)^85*1562500000000^69 ≤ 38715181^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912077 5000000000 38715181 1562500000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852677999/2000000000 : ℝ), (3525000289/5000000000 : ℝ), (-912077/5000000000 : ℝ)] ![(4373319191543/12500000000000 : ℝ), (4063185543169/6250000000000 : ℝ), (38715181/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852677999/2000000000 : ℝ)|^85 ≤ (4373319191543/12500000000000 : ℝ)^69
        have hw : |(852677999/2000000000 : ℝ)|=(852677999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3525000289/5000000000 : ℝ)|^85 ≤ (4063185543169/6250000000000 : ℝ)^69
        have hw : |(3525000289/5000000000 : ℝ)|=(3525000289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912077/5000000000 : ℝ)|^85 ≤ (38715181/1562500000000 : ℝ)^69
        have hw : |(-912077/5000000000 : ℝ)|=(912077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-208359977/2500000000 : ℝ)*x 0 + (241755011/1250000000 : ℝ)*x 1 + (-8520746077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208359977/2500000000 : ℝ)^85 ≤ (1171068374249/25000000000000 : ℝ)^69 := by
    have hnat : (208359977 : ℕ)^85*25000000000000^69 ≤ 1171068374249^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208359977 2500000000 1171068374249 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241755011/1250000000 : ℝ)^85 ≤ (13213205510351/100000000000000 : ℝ)^69 := by
    have hnat : (241755011 : ℕ)^85*100000000000000^69 ≤ 13213205510351^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241755011 1250000000 13213205510351 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8520746077/10000000000 : ℝ)^85 ≤ (5131407561179/6250000000000 : ℝ)^69 := by
    have hnat : (8520746077 : ℕ)^85*6250000000000^69 ≤ 5131407561179^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8520746077 10000000000 5131407561179 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208359977/2500000000 : ℝ), (241755011/1250000000 : ℝ), (-8520746077/10000000000 : ℝ)] ![(1171068374249/25000000000000 : ℝ), (13213205510351/100000000000000 : ℝ), (5131407561179/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208359977/2500000000 : ℝ)|^85 ≤ (1171068374249/25000000000000 : ℝ)^69
        have hw : |(-208359977/2500000000 : ℝ)|=(208359977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241755011/1250000000 : ℝ)|^85 ≤ (13213205510351/100000000000000 : ℝ)^69
        have hw : |(241755011/1250000000 : ℝ)|=(241755011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8520746077/10000000000 : ℝ)|^85 ≤ (5131407561179/6250000000000 : ℝ)^69
        have hw : |(-8520746077/10000000000 : ℝ)|=(8520746077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (952066679/10000000000 : ℝ)*x 0 + (-1834288063/10000000000 : ℝ)*x 1 + (-8520747239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952066679/10000000000 : ℝ)^85 ≤ (5518697760527/100000000000000 : ℝ)^69 := by
    have hnat : (952066679 : ℕ)^85*100000000000000^69 ≤ 5518697760527^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952066679 10000000000 5518697760527 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1834288063/10000000000 : ℝ)^85 ≤ (12378767445561/100000000000000 : ℝ)^69 := by
    have hnat : (1834288063 : ℕ)^85*100000000000000^69 ≤ 12378767445561^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834288063 10000000000 12378767445561 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8520747239/10000000000 : ℝ)^85 ≤ (4105126738587/5000000000000 : ℝ)^69 := by
    have hnat : (8520747239 : ℕ)^85*5000000000000^69 ≤ 4105126738587^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8520747239 10000000000 4105126738587 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(952066679/10000000000 : ℝ), (-1834288063/10000000000 : ℝ), (-8520747239/10000000000 : ℝ)] ![(5518697760527/100000000000000 : ℝ), (12378767445561/100000000000000 : ℝ), (4105126738587/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(952066679/10000000000 : ℝ)|^85 ≤ (5518697760527/100000000000000 : ℝ)^69
        have hw : |(952066679/10000000000 : ℝ)|=(952066679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1834288063/10000000000 : ℝ)|^85 ≤ (12378767445561/100000000000000 : ℝ)^69
        have hw : |(-1834288063/10000000000 : ℝ)|=(1834288063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8520747239/10000000000 : ℝ)|^85 ≤ (4105126738587/5000000000000 : ℝ)^69
        have hw : |(-8520747239/10000000000 : ℝ)|=(8520747239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6659677747/10000000000 : ℝ)*x 0 + (3553184677/10000000000 : ℝ)*x 1 + (215098751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6659677747/10000000000 : ℝ)^85 ≤ (30302944756519/50000000000000 : ℝ)^69 := by
    have hnat : (6659677747 : ℕ)^85*50000000000000^69 ≤ 30302944756519^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6659677747 10000000000 30302944756519 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3553184677/10000000000 : ℝ)^85 ≤ (27952020614889/100000000000000 : ℝ)^69 := by
    have hnat : (3553184677 : ℕ)^85*100000000000000^69 ≤ 27952020614889^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3553184677 10000000000 27952020614889 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215098751/1250000000 : ℝ)^85 ≤ (5721044927877/50000000000000 : ℝ)^69 := by
    have hnat : (215098751 : ℕ)^85*50000000000000^69 ≤ 5721044927877^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215098751 1250000000 5721044927877 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6659677747/10000000000 : ℝ), (3553184677/10000000000 : ℝ), (215098751/1250000000 : ℝ)] ![(30302944756519/50000000000000 : ℝ), (27952020614889/100000000000000 : ℝ), (5721044927877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6659677747/10000000000 : ℝ)|^85 ≤ (30302944756519/50000000000000 : ℝ)^69
        have hw : |(6659677747/10000000000 : ℝ)|=(6659677747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3553184677/10000000000 : ℝ)|^85 ≤ (27952020614889/100000000000000 : ℝ)^69
        have hw : |(3553184677/10000000000 : ℝ)|=(3553184677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215098751/1250000000 : ℝ)|^85 ≤ (5721044927877/50000000000000 : ℝ)^69
        have hw : |(215098751/1250000000 : ℝ)|=(215098751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4294245121/5000000000 : ℝ)*x 0 + (595837/2500000 : ℝ)*x 1 + (-162477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4294245121/5000000000 : ℝ)^85 ≤ (82907380218011/100000000000000 : ℝ)^69 := by
    have hnat : (4294245121 : ℕ)^85*100000000000000^69 ≤ 82907380218011^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294245121 5000000000 82907380218011 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595837/2500000 : ℝ)^85 ≤ (17090987653549/100000000000000 : ℝ)^69 := by
    have hnat : (595837 : ℕ)^85*100000000000000^69 ≤ 17090987653549^69*2500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595837 2500000 17090987653549 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162477/1250000000 : ℝ)^85 ≤ (1632123579/100000000000000 : ℝ)^69 := by
    have hnat : (162477 : ℕ)^85*100000000000000^69 ≤ 1632123579^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162477 1250000000 1632123579 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4294245121/5000000000 : ℝ), (595837/2500000 : ℝ), (-162477/1250000000 : ℝ)] ![(82907380218011/100000000000000 : ℝ), (17090987653549/100000000000000 : ℝ), (1632123579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4294245121/5000000000 : ℝ)|^85 ≤ (82907380218011/100000000000000 : ℝ)^69
        have hw : |(4294245121/5000000000 : ℝ)|=(4294245121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595837/2500000 : ℝ)|^85 ≤ (17090987653549/100000000000000 : ℝ)^69
        have hw : |(595837/2500000 : ℝ)|=(595837/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-162477/1250000000 : ℝ)|^85 ≤ (1632123579/100000000000000 : ℝ)^69
        have hw : |(-162477/1250000000 : ℝ)|=(162477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-657549431/10000000000 : ℝ)*x 0 + (2865001883/5000000000 : ℝ)*x 1 + (-1067491953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657549431/10000000000 : ℝ)^85 ≤ (3498040620313/100000000000000 : ℝ)^69 := by
    have hnat : (657549431 : ℕ)^85*100000000000000^69 ≤ 3498040620313^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657549431 10000000000 3498040620313 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2865001883/5000000000 : ℝ)^85 ≤ (25179371775193/50000000000000 : ℝ)^69 := by
    have hnat : (2865001883 : ℕ)^85*50000000000000^69 ≤ 25179371775193^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865001883 5000000000 25179371775193 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067491953/2000000000 : ℝ)^85 ≤ (11535803953863/25000000000000 : ℝ)^69 := by
    have hnat : (1067491953 : ℕ)^85*25000000000000^69 ≤ 11535803953863^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067491953 2000000000 11535803953863 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-657549431/10000000000 : ℝ), (2865001883/5000000000 : ℝ), (-1067491953/2000000000 : ℝ)] ![(3498040620313/100000000000000 : ℝ), (25179371775193/50000000000000 : ℝ), (11535803953863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-657549431/10000000000 : ℝ)|^85 ≤ (3498040620313/100000000000000 : ℝ)^69
        have hw : |(-657549431/10000000000 : ℝ)|=(657549431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2865001883/5000000000 : ℝ)|^85 ≤ (25179371775193/50000000000000 : ℝ)^69
        have hw : |(2865001883/5000000000 : ℝ)|=(2865001883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067491953/2000000000 : ℝ)|^85 ≤ (11535803953863/25000000000000 : ℝ)^69
        have hw : |(-1067491953/2000000000 : ℝ)|=(1067491953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1728538843/2500000000 : ℝ)*x 0 + (-844467531/10000000000 : ℝ)*x 1 + (-394214697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728538843/2500000000 : ℝ)^85 ≤ (63471270960827/100000000000000 : ℝ)^69 := by
    have hnat : (1728538843 : ℕ)^85*100000000000000^69 ≤ 63471270960827^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728538843 2500000000 63471270960827 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844467531/10000000000 : ℝ)^85 ≤ (2380371052933/50000000000000 : ℝ)^69 := by
    have hnat : (844467531 : ℕ)^85*50000000000000^69 ≤ 2380371052933^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844467531 10000000000 2380371052933 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394214697/1000000000 : ℝ)^85 ≤ (31767986925139/100000000000000 : ℝ)^69 := by
    have hnat : (394214697 : ℕ)^85*100000000000000^69 ≤ 31767986925139^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394214697 1000000000 31767986925139 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1728538843/2500000000 : ℝ), (-844467531/10000000000 : ℝ), (-394214697/1000000000 : ℝ)] ![(63471270960827/100000000000000 : ℝ), (2380371052933/50000000000000 : ℝ), (31767986925139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1728538843/2500000000 : ℝ)|^85 ≤ (63471270960827/100000000000000 : ℝ)^69
        have hw : |(1728538843/2500000000 : ℝ)|=(1728538843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844467531/10000000000 : ℝ)|^85 ≤ (2380371052933/50000000000000 : ℝ)^69
        have hw : |(-844467531/10000000000 : ℝ)|=(844467531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394214697/1000000000 : ℝ)|^85 ≤ (31767986925139/100000000000000 : ℝ)^69
        have hw : |(-394214697/1000000000 : ℝ)|=(394214697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (128386909/1000000000 : ℝ)*x 0 + (2015118033/2500000000 : ℝ)*x 1 + (1092143057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128386909/1000000000 : ℝ)^85 ≤ (3988144814463/50000000000000 : ℝ)^69 := by
    have hnat : (128386909 : ℕ)^85*50000000000000^69 ≤ 3988144814463^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128386909 1000000000 3988144814463 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015118033/2500000000 : ℝ)^85 ≤ (4792112294949/6250000000000 : ℝ)^69 := by
    have hnat : (2015118033 : ℕ)^85*6250000000000^69 ≤ 4792112294949^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015118033 2500000000 4792112294949 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092143057/5000000000 : ℝ)^85 ≤ (239842400623/1562500000000 : ℝ)^69 := by
    have hnat : (1092143057 : ℕ)^85*1562500000000^69 ≤ 239842400623^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092143057 5000000000 239842400623 1562500000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128386909/1000000000 : ℝ), (2015118033/2500000000 : ℝ), (1092143057/5000000000 : ℝ)] ![(3988144814463/50000000000000 : ℝ), (4792112294949/6250000000000 : ℝ), (239842400623/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128386909/1000000000 : ℝ)|^85 ≤ (3988144814463/50000000000000 : ℝ)^69
        have hw : |(128386909/1000000000 : ℝ)|=(128386909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015118033/2500000000 : ℝ)|^85 ≤ (4792112294949/6250000000000 : ℝ)^69
        have hw : |(2015118033/2500000000 : ℝ)|=(2015118033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092143057/5000000000 : ℝ)|^85 ≤ (239842400623/1562500000000 : ℝ)^69
        have hw : |(1092143057/5000000000 : ℝ)|=(1092143057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (578986777/625000000 : ℝ)*x 0 + (1404758119/10000000000 : ℝ)*x 1 + (-30308651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578986777/625000000 : ℝ)^85 ≤ (4550482459249/5000000000000 : ℝ)^69 := by
    have hnat : (578986777 : ℕ)^85*5000000000000^69 ≤ 4550482459249^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578986777 625000000 4550482459249 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404758119/10000000000 : ℝ)^85 ≤ (4455679495699/50000000000000 : ℝ)^69 := by
    have hnat : (1404758119 : ℕ)^85*50000000000000^69 ≤ 4455679495699^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404758119 10000000000 4455679495699 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30308651/10000000000 : ℝ)^85 ≤ (78991807583/100000000000000 : ℝ)^69 := by
    have hnat : (30308651 : ℕ)^85*100000000000000^69 ≤ 78991807583^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30308651 10000000000 78991807583 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578986777/625000000 : ℝ), (1404758119/10000000000 : ℝ), (-30308651/10000000000 : ℝ)] ![(4550482459249/5000000000000 : ℝ), (4455679495699/50000000000000 : ℝ), (78991807583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578986777/625000000 : ℝ)|^85 ≤ (4550482459249/5000000000000 : ℝ)^69
        have hw : |(578986777/625000000 : ℝ)|=(578986777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1404758119/10000000000 : ℝ)|^85 ≤ (4455679495699/50000000000000 : ℝ)^69
        have hw : |(1404758119/10000000000 : ℝ)|=(1404758119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30308651/10000000000 : ℝ)|^85 ≤ (78991807583/100000000000000 : ℝ)^69
        have hw : |(-30308651/10000000000 : ℝ)|=(30308651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-981550821/5000000000 : ℝ)*x 0 + (3911497093/10000000000 : ℝ)*x 1 + (-1232434547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981550821/5000000000 : ℝ)^85 ≤ (2691643175687/20000000000000 : ℝ)^69 := by
    have hnat : (981550821 : ℕ)^85*20000000000000^69 ≤ 2691643175687^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981550821 5000000000 2691643175687 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3911497093/10000000000 : ℝ)^85 ≤ (7865998582463/25000000000000 : ℝ)^69 := by
    have hnat : (3911497093 : ℕ)^85*25000000000000^69 ≤ 7865998582463^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3911497093 10000000000 7865998582463 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232434547/2000000000 : ℝ)^85 ≤ (55077789786761/100000000000000 : ℝ)^69 := by
    have hnat : (1232434547 : ℕ)^85*100000000000000^69 ≤ 55077789786761^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232434547 2000000000 55077789786761 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981550821/5000000000 : ℝ), (3911497093/10000000000 : ℝ), (-1232434547/2000000000 : ℝ)] ![(2691643175687/20000000000000 : ℝ), (7865998582463/25000000000000 : ℝ), (55077789786761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981550821/5000000000 : ℝ)|^85 ≤ (2691643175687/20000000000000 : ℝ)^69
        have hw : |(-981550821/5000000000 : ℝ)|=(981550821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3911497093/10000000000 : ℝ)|^85 ≤ (7865998582463/25000000000000 : ℝ)^69
        have hw : |(3911497093/10000000000 : ℝ)|=(3911497093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1232434547/2000000000 : ℝ)|^85 ≤ (55077789786761/100000000000000 : ℝ)^69
        have hw : |(-1232434547/2000000000 : ℝ)|=(1232434547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4503066341/10000000000 : ℝ)*x 0 + (-51025857/200000000 : ℝ)*x 1 + (-5134225167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503066341/10000000000 : ℝ)^85 ≤ (7485011120489/20000000000000 : ℝ)^69 := by
    have hnat : (4503066341 : ℕ)^85*20000000000000^69 ≤ 7485011120489^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503066341 10000000000 7485011120489 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51025857/200000000 : ℝ)^85 ≤ (2323311802873/12500000000000 : ℝ)^69 := by
    have hnat : (51025857 : ℕ)^85*12500000000000^69 ≤ 2323311802873^69*200000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51025857 200000000 2323311802873 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134225167/10000000000 : ℝ)^85 ≤ (43988449950837/100000000000000 : ℝ)^69 := by
    have hnat : (5134225167 : ℕ)^85*100000000000000^69 ≤ 43988449950837^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134225167 10000000000 43988449950837 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503066341/10000000000 : ℝ), (-51025857/200000000 : ℝ), (-5134225167/10000000000 : ℝ)] ![(7485011120489/20000000000000 : ℝ), (2323311802873/12500000000000 : ℝ), (43988449950837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503066341/10000000000 : ℝ)|^85 ≤ (7485011120489/20000000000000 : ℝ)^69
        have hw : |(4503066341/10000000000 : ℝ)|=(4503066341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51025857/200000000 : ℝ)|^85 ≤ (2323311802873/12500000000000 : ℝ)^69
        have hw : |(-51025857/200000000 : ℝ)|=(51025857/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5134225167/10000000000 : ℝ)|^85 ≤ (43988449950837/100000000000000 : ℝ)^69
        have hw : |(-5134225167/10000000000 : ℝ)|=(5134225167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2308133751/5000000000 : ℝ)*x 0 + (1127975501/2000000000 : ℝ)*x 1 + (1791961567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2308133751/5000000000 : ℝ)^85 ≤ (38587389107901/100000000000000 : ℝ)^69 := by
    have hnat : (2308133751 : ℕ)^85*100000000000000^69 ≤ 38587389107901^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308133751 5000000000 38587389107901 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127975501/2000000000 : ℝ)^85 ≤ (617309679099/1250000000000 : ℝ)^69 := by
    have hnat : (1127975501 : ℕ)^85*1250000000000^69 ≤ 617309679099^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127975501 2000000000 617309679099 1250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1791961567/10000000000 : ℝ)^85 ≤ (12027836552539/100000000000000 : ℝ)^69 := by
    have hnat : (1791961567 : ℕ)^85*100000000000000^69 ≤ 12027836552539^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791961567 10000000000 12027836552539 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2308133751/5000000000 : ℝ), (1127975501/2000000000 : ℝ), (1791961567/10000000000 : ℝ)] ![(38587389107901/100000000000000 : ℝ), (617309679099/1250000000000 : ℝ), (12027836552539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2308133751/5000000000 : ℝ)|^85 ≤ (38587389107901/100000000000000 : ℝ)^69
        have hw : |(2308133751/5000000000 : ℝ)|=(2308133751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127975501/2000000000 : ℝ)|^85 ≤ (617309679099/1250000000000 : ℝ)^69
        have hw : |(1127975501/2000000000 : ℝ)|=(1127975501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1791961567/10000000000 : ℝ)|^85 ≤ (12027836552539/100000000000000 : ℝ)^69
        have hw : |(1791961567/10000000000 : ℝ)|=(1791961567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324060_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3447353749/5000000000 : ℝ)*x 0 + (1939339619/5000000000 : ℝ)*x 1 + (-964759673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3447353749/5000000000 : ℝ)^85 ≤ (63251414986749/100000000000000 : ℝ)^69 := by
    have hnat : (3447353749 : ℕ)^85*100000000000000^69 ≤ 63251414986749^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3447353749 5000000000 63251414986749 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939339619/5000000000 : ℝ)^85 ≤ (31139111105971/100000000000000 : ℝ)^69 := by
    have hnat : (1939339619 : ℕ)^85*100000000000000^69 ≤ 31139111105971^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939339619 5000000000 31139111105971 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964759673/10000000000 : ℝ)^85 ≤ (2804736945827/50000000000000 : ℝ)^69 := by
    have hnat : (964759673 : ℕ)^85*50000000000000^69 ≤ 2804736945827^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964759673 10000000000 2804736945827 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3447353749/5000000000 : ℝ), (1939339619/5000000000 : ℝ), (-964759673/10000000000 : ℝ)] ![(63251414986749/100000000000000 : ℝ), (31139111105971/100000000000000 : ℝ), (2804736945827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3447353749/5000000000 : ℝ)|^85 ≤ (63251414986749/100000000000000 : ℝ)^69
        have hw : |(3447353749/5000000000 : ℝ)|=(3447353749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1939339619/5000000000 : ℝ)|^85 ≤ (31139111105971/100000000000000 : ℝ)^69
        have hw : |(1939339619/5000000000 : ℝ)|=(1939339619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964759673/10000000000 : ℝ)|^85 ≤ (2804736945827/50000000000000 : ℝ)^69
        have hw : |(-964759673/10000000000 : ℝ)|=(964759673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324060 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1267417919/10000000000 : ℝ)*X 0 0+(2261817087/5000000000 : ℝ)*X 0 1+(-1222178071/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((904726621/2000000000 : ℝ)*X 1 0+(-633708499/5000000000 : ℝ)*X 1 1+(-6110891991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-19043201/125000000 : ℝ)*X 0 0+(1543500823/10000000000 : ℝ)*X 0 1+(-4177705853/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((298189513/1250000000 : ℝ)*X 1 0+(-135037971/2500000000 : ℝ)*X 1 1+(-8355412009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1013649369/5000000000 : ℝ)*X 2 0+(2018986859/2500000000 : ℝ)*X 2 1+(1434252213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((852677999/2000000000 : ℝ)*X 0 0+(3525000289/5000000000 : ℝ)*X 0 1+(-912077/5000000000 : ℝ)*X 0 2+(852677999/2000000000 : ℝ)*X 1 0+(3525000289/5000000000 : ℝ)*X 1 1+(-912077/5000000000 : ℝ)*X 1 2+(852677999/2000000000 : ℝ)*X 2 0+(3525000289/5000000000 : ℝ)*X 2 1+(-912077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-208359977/2500000000 : ℝ)*X 0 0+(241755011/1250000000 : ℝ)*X 0 1+(-8520746077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((952066679/10000000000 : ℝ)*X 1 0+(-1834288063/10000000000 : ℝ)*X 1 1+(-8520747239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6659677747/10000000000 : ℝ)*X 2 0+(3553184677/10000000000 : ℝ)*X 2 1+(215098751/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4294245121/5000000000 : ℝ)*X 0 0+(595837/2500000 : ℝ)*X 0 1+(-162477/1250000000 : ℝ)*X 0 2+(4294245121/5000000000 : ℝ)*X 1 0+(595837/2500000 : ℝ)*X 1 1+(-162477/1250000000 : ℝ)*X 1 2+(4294245121/5000000000 : ℝ)*X 2 0+(595837/2500000 : ℝ)*X 2 1+(-162477/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-657549431/10000000000 : ℝ)*X 0 0+(2865001883/5000000000 : ℝ)*X 0 1+(-1067491953/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1728538843/2500000000 : ℝ)*X 1 0+(-844467531/10000000000 : ℝ)*X 1 1+(-394214697/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((128386909/1000000000 : ℝ)*X 2 0+(2015118033/2500000000 : ℝ)*X 2 1+(1092143057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((578986777/625000000 : ℝ)*X 0 0+(1404758119/10000000000 : ℝ)*X 0 1+(-30308651/10000000000 : ℝ)*X 0 2+(578986777/625000000 : ℝ)*X 1 0+(1404758119/10000000000 : ℝ)*X 1 1+(-30308651/10000000000 : ℝ)*X 1 2+(578986777/625000000 : ℝ)*X 2 0+(1404758119/10000000000 : ℝ)*X 2 1+(-30308651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((68627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84684820325523635733/6250000000000000000000000 : ℝ) := by norm_num
    linear_combination (151853940591/500000000000 : ℝ)*(base5) + (1167393026113/1000000000000 : ℝ)*(base7) + (1183309/1000000000000 : ℝ)*(base59) + (63253614459/40000000000 : ℝ)*(major_s0_0) + (63253614459/40000000000 : ℝ)*(major_s0_1) + (63253614459/40000000000 : ℝ)*(major_s0_2) + (3839611/500000000000 : ℝ)*(sp_s0_0) + (5139353/1000000000000 : ℝ)*(sp_s0_1) + (859383622347/500000000000 : ℝ)*(sp_s0_7) + (1718807415039/1000000000000 : ℝ)*(sp_s0_8) + (2022532423851/1000000000000 : ℝ)*(sp_s0_9) + (415299496461/250000000000 : ℝ)*(sp_s0_13) + (24809377/500000000000 : ℝ)*(sp_s0_14) + (11988277/1000000000000 : ℝ)*(sp_s0_15) + (797512840913/1000000000000 : ℝ)*(f.failure) + (171882454267/100000000000 : ℝ)*(f.sum) + (3364254986033/20000000000000000000000000 : ℝ)*base62 + (187120962748929/400000000000000000000000000 : ℝ)*base64 + (176695036108929/400000000000000000000000000 : ℝ)*base67 + (7144787702033/40000000000000000000000000 : ℝ)*base68 + (165225185889259/400000000000000000000000000 : ℝ)*base70 + (159956062091071/400000000000000000000000000 : ℝ)*base72 + (9655623038033/40000000000000000000000000 : ℝ)*base74 + (10895155238033/40000000000000000000000000 : ℝ)*base76 + (1942078048929/200000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (23323/25000000000000000 : ℝ)*base87 + (23323/25000000000000000 : ℝ)*base89 + (23323/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17097/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17097/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5248378717983590679561/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513597/1000000000000 : ℝ)*(base5) + (145142396267/125000000000 : ℝ)*(base7) + (6664093/1000000000000 : ℝ)*(base12) + (3600722999/40000000000 : ℝ)*(base60) + (149578849393/100000000000 : ℝ)*(major_s0_0) + (149578849393/100000000000 : ℝ)*(major_s0_1) + (149578849393/100000000000 : ℝ)*(major_s0_2) + (331047/500000000000 : ℝ)*(sp_s0_1) + (5806913/100000000000 : ℝ)*(sp_s0_7) + (1594265729409/1000000000000 : ℝ)*(sp_s0_14) + (1594329800539/1000000000000 : ℝ)*(sp_s0_15) + (1594330976229/1000000000000 : ℝ)*(sp_s0_16) + (957741019869/500000000000 : ℝ)*(sp_s0_20) + (23330167/1000000000000 : ℝ)*(sp_s0_27) + (377183356683/500000000000 : ℝ)*(f.failure) + (199291307829/125000000000 : ℝ)*(f.sum) + (33655741155891/50000000000000000000000000 : ℝ)*base62 + (387812737530083/1000000000000000000000000000 : ℝ)*base64 + (6496271830083/1000000000000000000000000000 : ℝ)*base67 + (98953007225891/100000000000000000000000000 : ℝ)*base68 + (173681975588993/1000000000000000000000000000 : ℝ)*base70 + (725229942030083/1000000000000000000000000000 : ℝ)*base73 + (47174149345891/100000000000000000000000000 : ℝ)*base74 + (27474170375891/100000000000000000000000000 : ℝ)*base76 + (7564293319917/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (7993/12500000000000000 : ℝ)*base87 + (7993/12500000000000000 : ℝ)*base89 + (7993/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-58521/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-58521/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24075524223155954507193/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (843174087417/1000000000000 : ℝ)*(base7) + (18335556627/250000000000 : ℝ)*(base39) + (140210594377/500000000000 : ℝ)*(base43) + (763523/500000000000 : ℝ)*(base50) + (1503872614121/1000000000000 : ℝ)*(major_s0_0) + (152931428171/125000000000 : ℝ)*(major_s0_1) + (1503872614121/1000000000000 : ℝ)*(major_s0_2) + (13743831/1000000000000 : ℝ)*(sp_s0_0) + (8189437/125000000000 : ℝ)*(sp_s0_9) + (1881539/500000000000 : ℝ)*(sp_s0_20) + (150203156587/100000000000 : ℝ)*(sp_s0_21) + (356493299691/200000000000 : ℝ)*(sp_s0_22) + (300395958841/200000000000 : ℝ)*(sp_s0_23) + (1601614078813/1000000000000 : ℝ)*(sp_s0_27) + (379221877237/500000000000 : ℝ)*(f.failure) + (356493299691/200000000000 : ℝ)*(f.sum) + (66617722279357/1000000000000000000000000000 : ℝ)*base63 + (5025245983268949/10000000000000000000000000000 : ℝ)*base65 + (351643715281601/1250000000000000000000000000 : ℝ)*base67 + (211020465942427/1000000000000000000000000000 : ℝ)*base68 + (551079294844679/10000000000000000000000000000 : ℝ)*base71 + (7338266516731051/10000000000000000000000000000 : ℝ)*base73 + (13045495334777/125000000000000000000000000 : ℝ)*base74 + (531648162957573/1000000000000000000000000000 : ℝ)*base77 + (5470947404983859/10000000000000000000000000000 : ℝ)*base79 + (2827/12500000000000000 : ℝ)*base87 + (9673/12500000000000000 : ℝ)*base88 + (2827/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (68627/100000 : ℝ) ^ (21/4 : ℝ) ≤ (6927377097378965007/50000000000000000000 : ℝ) := by
    have hpowers : (68627/100000 : ℝ)^21 ≤ (6927377097378965007/50000000000000000000 : ℝ)^4 := by
      have hnat : (68627 : ℕ)^21*50000000000000000000^4 ≤ 6927377097378965007^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68627 100000 6927377097378965007 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68627/100000 : ℝ)) (X := (6927377097378965007/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (56927377097378965007/50000000000000000000 : ℝ) ≤ (10250228719994421/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (56927377097378965007/50000000000000000000 : ℝ)^4 ≤ (10250228719994421/10000000000000000 : ℝ)^21 := by
      have hnat : (56927377097378965007 : ℕ)^4*10000000000000000^21 ≤ 10250228719994421^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56927377097378965007 50000000000000000000 10250228719994421 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10250228719994421/10000000000000000 : ℝ)) (X := (56927377097378965007/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (31927377097378965007/25000000000000000000 : ℝ) ≤ (2619226194795769/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (31927377097378965007/25000000000000000000 : ℝ)^4 ≤ (2619226194795769/2500000000000000 : ℝ)^21 := by
      have hnat : (31927377097378965007 : ℕ)^4*2500000000000000^21 ≤ 2619226194795769^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31927377097378965007 25000000000000000000 2619226194795769 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2619226194795769/2500000000000000 : ℝ)) (X := (31927377097378965007/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(250228719994421/6862700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(45335211837731/1372540000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (68627/100000 : ℝ)) (alpha := (250228719994421/6862700000000000 : ℝ)) (beta := (45335211837731/1372540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68627/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(250228719994421/6862700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(45335211837731/1372540000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17097/25000 : ℝ) ^ (21/4 : ℝ) ≤ (2720661346858571629/20000000000000000000 : ℝ) := by
    have hpowers : (17097/25000 : ℝ)^21 ≤ (2720661346858571629/20000000000000000000 : ℝ)^4 := by
      have hnat : (17097 : ℕ)^21*20000000000000000000^4 ≤ 2720661346858571629^4*25000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17097 25000 2720661346858571629 20000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17097/25000 : ℝ)) (X := (2720661346858571629/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (22720661346858571629/20000000000000000000 : ℝ) ≤ (2049182588785147/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (22720661346858571629/20000000000000000000 : ℝ)^4 ≤ (2049182588785147/2000000000000000 : ℝ)^21 := by
      have hnat : (22720661346858571629 : ℕ)^4*2000000000000000^21 ≤ 2049182588785147^21*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22720661346858571629 20000000000000000000 2049182588785147 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2049182588785147/2000000000000000 : ℝ)) (X := (22720661346858571629/20000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12720661346858571629/10000000000000000000 : ℝ) ≤ (81789327659671/78125000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (12720661346858571629/10000000000000000000 : ℝ)^4 ≤ (81789327659671/78125000000000 : ℝ)^21 := by
      have hnat : (12720661346858571629 : ℕ)^4*78125000000000^21 ≤ 81789327659671^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12720661346858571629 10000000000000000000 81789327659671 78125000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (81789327659671/78125000000000 : ℝ)) (X := (12720661346858571629/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(49182588785147/1367760000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(74373665504051/2279600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (17097/25000 : ℝ)) (alpha := (49182588785147/1367760000000000 : ℝ)) (beta := (74373665504051/2279600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17097/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(49182588785147/1367760000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(74373665504051/2279600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (58521/100000 : ℝ) ^ (21/4 : ℝ) ≤ (300162637250558447/5000000000000000000 : ℝ) := by
    have hpowers : (58521/100000 : ℝ)^21 ≤ (300162637250558447/5000000000000000000 : ℝ)^4 := by
      have hnat : (58521 : ℕ)^21*5000000000000000000^4 ≤ 300162637250558447^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58521 100000 300162637250558447 5000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58521/100000 : ℝ)) (X := (300162637250558447/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5300162637250558447/5000000000000000000 : ℝ) ≤ (505583285214639/500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (5300162637250558447/5000000000000000000 : ℝ)^4 ≤ (505583285214639/500000000000000 : ℝ)^21 := by
      have hnat : (5300162637250558447 : ℕ)^4*500000000000000^21 ≤ 505583285214639^21*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5300162637250558447 5000000000000000000 505583285214639 500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505583285214639/500000000000000 : ℝ)) (X := (5300162637250558447/5000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2800162637250558447/2500000000000000000 : ℝ) ≤ (1277290491729639/1250000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2800162637250558447/2500000000000000000 : ℝ)^4 ≤ (1277290491729639/1250000000000000 : ℝ)^21 := by
      have hnat : (2800162637250558447 : ℕ)^4*1250000000000000^21 ≤ 1277290491729639^21*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2800162637250558447 2500000000000000000 1277290491729639 1250000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1277290491729639/1250000000000000 : ℝ)) (X := (2800162637250558447/2500000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(5583285214639/292605000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8888185795361/487675000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (58521/100000 : ℝ)) (alpha := (5583285214639/292605000000000 : ℝ)) (beta := (8888185795361/487675000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (58521/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(5583285214639/292605000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8888185795361/487675000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-981550821/5000000000 : ℝ)*X 0 0+(3911497093/10000000000 : ℝ)*X 0 1+(-1232434547/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4503066341/10000000000 : ℝ)*X 1 0+(-51025857/200000000 : ℝ)*X 1 1+(-5134225167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2308133751/5000000000 : ℝ)*X 2 0+(1127975501/2000000000 : ℝ)*X 2 1+(1791961567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3447353749/5000000000 : ℝ)*X 0 0+(1939339619/5000000000 : ℝ)*X 0 1+(-964759673/10000000000 : ℝ)*X 0 2+(3447353749/5000000000 : ℝ)*X 1 0+(1939339619/5000000000 : ℝ)*X 1 1+(-964759673/10000000000 : ℝ)*X 1 2+(3447353749/5000000000 : ℝ)*X 2 0+(1939339619/5000000000 : ℝ)*X 2 1+(-964759673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324060_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-52860572847522967630984948366351243/5960383250321093750000000000000000 : ℝ) := by norm_num
    linear_combination (11159/250000000000 : ℝ)*(base5) + (65349/1000000000000 : ℝ)*(base7) + (13289/250000000000 : ℝ)*(base8) + (3133/50000000000 : ℝ)*(base18) + (34601/1000000000000 : ℝ)*(base29) + (151540866057/500000000000 : ℝ)*(base39) + (29709/1000000000000 : ℝ)*(base43) + (402509822939/1000000000000 : ℝ)*(base59) + (49571/25000 : ℝ)*(major_s1_0) + (1982839970291/1000000000000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (591243532491/200000000000 : ℝ)*(sp_s1_0) + (147810884133/50000000000 : ℝ)*(sp_s1_1) + (2956217760247/1000000000000 : ℝ)*(sp_s1_2) + (15624999783/15625000000 : ℝ)*(sp_s1_6) + (73905443633/25000000000 : ℝ)*(f.sum) + (11160636403062347773/26680894320000000000000000000000 : ℝ)*base62 + (41057194163703/195070000000000000000000000 : ℝ)*base65 + (223209410255199/2279600000000000000000000000 : ℝ)*base66 + (52962216954389/146302500000000000000000000 : ℝ)*base68 + (887495715843343977/1673383611250000000000000000000 : ℝ)*base71 + (78408343160827/171567500000000000000000000 : ℝ)*base72 + (54220350609743/1367760000000000000000000000 : ℝ)*base74 + (17647597155157/686270000000000000000000000 : ℝ)*base76 + (22481260074153237853/156442109200000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324064_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2972926593/10000000000 : ℝ)*x 0 + (-3574448297/10000000000 : ℝ)*x 1 + (-5641447797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2972926593/10000000000 : ℝ)^85 ≤ (22440059132791/100000000000000 : ℝ)^69 := by
    have hnat : (2972926593 : ℕ)^85*100000000000000^69 ≤ 22440059132791^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972926593 10000000000 22440059132791 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574448297/10000000000 : ℝ)^85 ≤ (28158227533093/100000000000000 : ℝ)^69 := by
    have hnat : (3574448297 : ℕ)^85*100000000000000^69 ≤ 28158227533093^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574448297 10000000000 28158227533093 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641447797/10000000000 : ℝ)^85 ≤ (49401713324237/100000000000000 : ℝ)^69 := by
    have hnat : (5641447797 : ℕ)^85*100000000000000^69 ≤ 49401713324237^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641447797 10000000000 49401713324237 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2972926593/10000000000 : ℝ), (-3574448297/10000000000 : ℝ), (-5641447797/10000000000 : ℝ)] ![(22440059132791/100000000000000 : ℝ), (28158227533093/100000000000000 : ℝ), (49401713324237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2972926593/10000000000 : ℝ)|^85 ≤ (22440059132791/100000000000000 : ℝ)^69
        have hw : |(-2972926593/10000000000 : ℝ)|=(2972926593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3574448297/10000000000 : ℝ)|^85 ≤ (28158227533093/100000000000000 : ℝ)^69
        have hw : |(-3574448297/10000000000 : ℝ)|=(3574448297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5641447797/10000000000 : ℝ)|^85 ≤ (49401713324237/100000000000000 : ℝ)^69
        have hw : |(-5641447797/10000000000 : ℝ)|=(5641447797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324064_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1685736157/5000000000 : ℝ)*x 0 + (5299445803/10000000000 : ℝ)*x 1 + (-3564286963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1685736157/5000000000 : ℝ)^85 ≤ (655041021973/2500000000000 : ℝ)^69 := by
    have hnat : (1685736157 : ℕ)^85*2500000000000^69 ≤ 655041021973^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685736157 5000000000 655041021973 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5299445803/10000000000 : ℝ)^85 ≤ (9147741623463/20000000000000 : ℝ)^69 := by
    have hnat : (5299445803 : ℕ)^85*20000000000000^69 ≤ 9147741623463^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5299445803 10000000000 9147741623463 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3564286963/10000000000 : ℝ)^85 ≤ (28059650989531/100000000000000 : ℝ)^69 := by
    have hnat : (3564286963 : ℕ)^85*100000000000000^69 ≤ 28059650989531^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3564286963 10000000000 28059650989531 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1685736157/5000000000 : ℝ), (5299445803/10000000000 : ℝ), (-3564286963/10000000000 : ℝ)] ![(655041021973/2500000000000 : ℝ), (9147741623463/20000000000000 : ℝ), (28059650989531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1685736157/5000000000 : ℝ)|^85 ≤ (655041021973/2500000000000 : ℝ)^69
        have hw : |(1685736157/5000000000 : ℝ)|=(1685736157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5299445803/10000000000 : ℝ)|^85 ≤ (9147741623463/20000000000000 : ℝ)^69
        have hw : |(5299445803/10000000000 : ℝ)|=(5299445803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3564286963/10000000000 : ℝ)|^85 ≤ (28059650989531/100000000000000 : ℝ)^69
        have hw : |(-3564286963/10000000000 : ℝ)|=(3564286963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324064_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (624672339/1000000000 : ℝ)*x 0 + (-1741009093/5000000000 : ℝ)*x 1 + (2341926399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624672339/1000000000 : ℝ)^85 ≤ (11202044447181/20000000000000 : ℝ)^69 := by
    have hnat : (624672339 : ℕ)^85*20000000000000^69 ≤ 11202044447181^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624672339 1000000000 11202044447181 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741009093/5000000000 : ℝ)^85 ≤ (13631980636733/50000000000000 : ℝ)^69 := by
    have hnat : (1741009093 : ℕ)^85*50000000000000^69 ≤ 13631980636733^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741009093 5000000000 13631980636733 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341926399/10000000000 : ℝ)^85 ≤ (1672581647969/10000000000000 : ℝ)^69 := by
    have hnat : (2341926399 : ℕ)^85*10000000000000^69 ≤ 1672581647969^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341926399 10000000000 1672581647969 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(624672339/1000000000 : ℝ), (-1741009093/5000000000 : ℝ), (2341926399/10000000000 : ℝ)] ![(11202044447181/20000000000000 : ℝ), (13631980636733/50000000000000 : ℝ), (1672581647969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(624672339/1000000000 : ℝ)|^85 ≤ (11202044447181/20000000000000 : ℝ)^69
        have hw : |(624672339/1000000000 : ℝ)|=(624672339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741009093/5000000000 : ℝ)|^85 ≤ (13631980636733/50000000000000 : ℝ)^69
        have hw : |(-1741009093/5000000000 : ℝ)|=(1741009093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2341926399/10000000000 : ℝ)|^85 ≤ (1672581647969/10000000000000 : ℝ)^69
        have hw : |(2341926399/10000000000 : ℝ)|=(2341926399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324064 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2972926593/10000000000 : ℝ)*X 0 0+(-3574448297/10000000000 : ℝ)*X 0 1+(-5641447797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1685736157/5000000000 : ℝ)*X 1 0+(5299445803/10000000000 : ℝ)*X 1 1+(-3564286963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((624672339/1000000000 : ℝ)*X 2 0+(-1741009093/5000000000 : ℝ)*X 2 1+(2341926399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-22154628701465129448950712861/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1127474738547/1000000000000 : ℝ)*(base1) + (63737358137/500000000000 : ℝ)*(base7) + (91927/500000000000 : ℝ)*(base15) + (16143/200000000000 : ℝ)*(base17) + (22113/500000000000 : ℝ)*(base33) + (147243229659/100000000000 : ℝ)*(base39) + (698985733069/1000000000000 : ℝ)*(base40) + (146172016597/200000000000 : ℝ)*(base60) + (991419977887/500000000000 : ℝ)*(major_s0_0) + (49571/25000 : ℝ)*(major_s0_1) + (49571/25000 : ℝ)*(major_s0_2) + (4010847491569/1000000000000 : ℝ)*(sp_s0_0) + (2883372444227/1000000000000 : ℝ)*(sp_s0_1) + (720843177199/250000000000 : ℝ)*(sp_s0_2) + (1441686376511/500000000000 : ℝ)*(f.sum) + (755425177/10000000000000000000000 : ℝ)*base63 + (1246692047/10000000000000000000000 : ℝ)*base64 + (222729623754293/10000000000000000000000 : ℝ)*base67 + (1436499761/5000000000000000000000 : ℝ)*base69 + (341672903659469/500000000000000000000000000 : ℝ)*base70 + (111368328505096059597/5000000000000000000000000000 : ℝ)*base73 + (5156731/125000000000000000000 : ℝ)*base74 + (83598234809469/500000000000000000000000000 : ℝ)*base76 + (111367068511393559597/5000000000000000000000000000 : ℝ)*base79 + (22273/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b033 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=60 ∨ c=61 ∨ c=62 ∨ c=63 ∨ c=64 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact collision_c324060 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324061 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c324064 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
