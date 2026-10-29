-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b037
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:51.30866+00:00
-- url     : https://prove2.me/submissions/7b1dc100-6574-418f-9667-ef418ea460fc

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309082_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309082_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309082_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309083_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309083_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309083_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309083_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c309082 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c309082_s0 p hpa hpb X hX
  have h1 := collision_c309082_s1 p hpa hpb X hX h0
  exact collision_c309082_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c309083 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c309083_s0 p hpa hpb X hX
  have h1 := collision_c309083_s1 p hpa hpb X hX h0
  have h2 := collision_c309083_s2 p hpa hpb X hX h1
  exact collision_c309083_s3 p hpa hpb X hX h2

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
theorem collision_support_c309081_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4465721483/10000000000 : ℝ)*x 0 + (2713481643/10000000000 : ℝ)*x 1 + (5529728329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465721483/10000000000 : ℝ)^35 ≤ (109902062563/312500000000 : ℝ)^27 := by
    have hnat : (4465721483 : ℕ)^35*312500000000^27 ≤ 109902062563^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465721483 10000000000 109902062563 312500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713481643/10000000000 : ℝ)^35 ≤ (3687338419531/20000000000000 : ℝ)^27 := by
    have hnat : (2713481643 : ℕ)^35*20000000000000^27 ≤ 3687338419531^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713481643 10000000000 3687338419531 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529728329/10000000000 : ℝ)^35 ≤ (23197323933277/50000000000000 : ℝ)^27 := by
    have hnat : (5529728329 : ℕ)^35*50000000000000^27 ≤ 23197323933277^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529728329 10000000000 23197323933277 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4465721483/10000000000 : ℝ), (2713481643/10000000000 : ℝ), (5529728329/10000000000 : ℝ)] ![(109902062563/312500000000 : ℝ), (3687338419531/20000000000000 : ℝ), (23197323933277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4465721483/10000000000 : ℝ)|^35 ≤ (109902062563/312500000000 : ℝ)^27
        have hw : |(-4465721483/10000000000 : ℝ)|=(4465721483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713481643/10000000000 : ℝ)|^35 ≤ (3687338419531/20000000000000 : ℝ)^27
        have hw : |(2713481643/10000000000 : ℝ)|=(2713481643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529728329/10000000000 : ℝ)|^35 ≤ (23197323933277/50000000000000 : ℝ)^27
        have hw : |(5529728329/10000000000 : ℝ)|=(5529728329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1014090009/2500000000 : ℝ)*x 0 + (701314741/1000000000 : ℝ)*x 1 + (-139344317/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014090009/2500000000 : ℝ)^35 ≤ (6209530804477/20000000000000 : ℝ)^27 := by
    have hnat : (1014090009 : ℕ)^35*20000000000000^27 ≤ 6209530804477^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014090009 2500000000 6209530804477 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701314741/1000000000 : ℝ)^35 ≤ (63133163320261/100000000000000 : ℝ)^27 := by
    have hnat : (701314741 : ℕ)^35*100000000000000^27 ≤ 63133163320261^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701314741 1000000000 63133163320261 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139344317/1250000000 : ℝ)^35 ≤ (5819182643897/100000000000000 : ℝ)^27 := by
    have hnat : (139344317 : ℕ)^35*100000000000000^27 ≤ 5819182643897^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139344317 1250000000 5819182643897 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1014090009/2500000000 : ℝ), (701314741/1000000000 : ℝ), (-139344317/1250000000 : ℝ)] ![(6209530804477/20000000000000 : ℝ), (63133163320261/100000000000000 : ℝ), (5819182643897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1014090009/2500000000 : ℝ)|^35 ≤ (6209530804477/20000000000000 : ℝ)^27
        have hw : |(1014090009/2500000000 : ℝ)|=(1014090009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701314741/1000000000 : ℝ)|^35 ≤ (63133163320261/100000000000000 : ℝ)^27
        have hw : |(701314741/1000000000 : ℝ)|=(701314741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139344317/1250000000 : ℝ)|^35 ≤ (5819182643897/100000000000000 : ℝ)^27
        have hw : |(-139344317/1250000000 : ℝ)|=(139344317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1222676129/2500000000 : ℝ)*x 0 + (345412323/2000000000 : ℝ)*x 1 + (5873620787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222676129/2500000000 : ℝ)^35 ≤ (39567018700467/100000000000000 : ℝ)^27 := by
    have hnat : (1222676129 : ℕ)^35*100000000000000^27 ≤ 39567018700467^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222676129 2500000000 39567018700467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345412323/2000000000 : ℝ)^35 ≤ (513209836229/5000000000000 : ℝ)^27 := by
    have hnat : (345412323 : ℕ)^35*5000000000000^27 ≤ 513209836229^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345412323 2000000000 513209836229 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5873620787/10000000000 : ℝ)^35 ≤ (50168784555147/100000000000000 : ℝ)^27 := by
    have hnat : (5873620787 : ℕ)^35*100000000000000^27 ≤ 50168784555147^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5873620787 10000000000 50168784555147 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1222676129/2500000000 : ℝ), (345412323/2000000000 : ℝ), (5873620787/10000000000 : ℝ)] ![(39567018700467/100000000000000 : ℝ), (513209836229/5000000000000 : ℝ), (50168784555147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1222676129/2500000000 : ℝ)|^35 ≤ (39567018700467/100000000000000 : ℝ)^27
        have hw : |(-1222676129/2500000000 : ℝ)|=(1222676129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345412323/2000000000 : ℝ)|^35 ≤ (513209836229/5000000000000 : ℝ)^27
        have hw : |(345412323/2000000000 : ℝ)|=(345412323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5873620787/10000000000 : ℝ)|^35 ≤ (50168784555147/100000000000000 : ℝ)^27
        have hw : |(5873620787/10000000000 : ℝ)|=(5873620787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4800795167/10000000000 : ℝ)*x 0 + (-302307713/1250000000 : ℝ)*x 1 + (2723277653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4800795167/10000000000 : ℝ)^35 ≤ (38626686168969/100000000000000 : ℝ)^27 := by
    have hnat : (4800795167 : ℕ)^35*100000000000000^27 ≤ 38626686168969^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800795167 10000000000 38626686168969 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302307713/1250000000 : ℝ)^35 ≤ (15881231164679/100000000000000 : ℝ)^27 := by
    have hnat : (302307713 : ℕ)^35*100000000000000^27 ≤ 15881231164679^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302307713 1250000000 15881231164679 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723277653/5000000000 : ℝ)^35 ≤ (22746041328411/50000000000000 : ℝ)^27 := by
    have hnat : (2723277653 : ℕ)^35*50000000000000^27 ≤ 22746041328411^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723277653 5000000000 22746041328411 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4800795167/10000000000 : ℝ), (-302307713/1250000000 : ℝ), (2723277653/5000000000 : ℝ)] ![(38626686168969/100000000000000 : ℝ), (15881231164679/100000000000000 : ℝ), (22746041328411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4800795167/10000000000 : ℝ)|^35 ≤ (38626686168969/100000000000000 : ℝ)^27
        have hw : |(4800795167/10000000000 : ℝ)|=(4800795167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302307713/1250000000 : ℝ)|^35 ≤ (15881231164679/100000000000000 : ℝ)^27
        have hw : |(-302307713/1250000000 : ℝ)|=(302307713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723277653/5000000000 : ℝ)|^35 ≤ (22746041328411/50000000000000 : ℝ)^27
        have hw : |(2723277653/5000000000 : ℝ)|=(2723277653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1540766973/5000000000 : ℝ)*x 0 + (4038355559/5000000000 : ℝ)*x 1 + (-285488717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540766973/5000000000 : ℝ)^35 ≤ (1087077490603/5000000000000 : ℝ)^27 := by
    have hnat : (1540766973 : ℕ)^35*5000000000000^27 ≤ 1087077490603^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540766973 5000000000 1087077490603 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4038355559/5000000000 : ℝ)^35 ≤ (9476729910049/12500000000000 : ℝ)^27 := by
    have hnat : (4038355559 : ℕ)^35*12500000000000^27 ≤ 9476729910049^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038355559 5000000000 9476729910049 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285488717/5000000000 : ℝ)^35 ≤ (488922178931/20000000000000 : ℝ)^27 := by
    have hnat : (285488717 : ℕ)^35*20000000000000^27 ≤ 488922178931^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285488717 5000000000 488922178931 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1540766973/5000000000 : ℝ), (4038355559/5000000000 : ℝ), (-285488717/5000000000 : ℝ)] ![(1087077490603/5000000000000 : ℝ), (9476729910049/12500000000000 : ℝ), (488922178931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1540766973/5000000000 : ℝ)|^35 ≤ (1087077490603/5000000000000 : ℝ)^27
        have hw : |(1540766973/5000000000 : ℝ)|=(1540766973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4038355559/5000000000 : ℝ)|^35 ≤ (9476729910049/12500000000000 : ℝ)^27
        have hw : |(4038355559/5000000000 : ℝ)|=(4038355559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285488717/5000000000 : ℝ)|^35 ≤ (488922178931/20000000000000 : ℝ)^27
        have hw : |(-285488717/5000000000 : ℝ)|=(285488717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (687955337/5000000000 : ℝ)*x 0 + (5144550851/10000000000 : ℝ)*x 1 + (1173588533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687955337/5000000000 : ℝ)^35 ≤ (7644651965743/100000000000000 : ℝ)^27 := by
    have hnat : (687955337 : ℕ)^35*100000000000000^27 ≤ 7644651965743^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687955337 5000000000 7644651965743 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144550851/10000000000 : ℝ)^35 ≤ (330073620937/781250000000 : ℝ)^27 := by
    have hnat : (5144550851 : ℕ)^35*781250000000^27 ≤ 330073620937^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144550851 10000000000 330073620937 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173588533/2000000000 : ℝ)^35 ≤ (50105924543371/100000000000000 : ℝ)^27 := by
    have hnat : (1173588533 : ℕ)^35*100000000000000^27 ≤ 50105924543371^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173588533 2000000000 50105924543371 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(687955337/5000000000 : ℝ), (5144550851/10000000000 : ℝ), (1173588533/2000000000 : ℝ)] ![(7644651965743/100000000000000 : ℝ), (330073620937/781250000000 : ℝ), (50105924543371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(687955337/5000000000 : ℝ)|^35 ≤ (7644651965743/100000000000000 : ℝ)^27
        have hw : |(687955337/5000000000 : ℝ)|=(687955337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144550851/10000000000 : ℝ)|^35 ≤ (330073620937/781250000000 : ℝ)^27
        have hw : |(5144550851/10000000000 : ℝ)|=(5144550851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173588533/2000000000 : ℝ)|^35 ≤ (50105924543371/100000000000000 : ℝ)^27
        have hw : |(1173588533/2000000000 : ℝ)|=(1173588533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2045721779/5000000000 : ℝ)*x 0 + (835349981/5000000000 : ℝ)*x 1 + (103693101/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045721779/5000000000 : ℝ)^35 ≤ (15698097866273/50000000000000 : ℝ)^27 := by
    have hnat : (2045721779 : ℕ)^35*50000000000000^27 ≤ 15698097866273^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045721779 5000000000 15698097866273 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835349981/5000000000 : ℝ)^35 ≤ (4916048510153/50000000000000 : ℝ)^27 := by
    have hnat : (835349981 : ℕ)^35*50000000000000^27 ≤ 4916048510153^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835349981 5000000000 4916048510153 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103693101/156250000 : ℝ)^35 ≤ (5877170723531/10000000000000 : ℝ)^27 := by
    have hnat : (103693101 : ℕ)^35*10000000000000^27 ≤ 5877170723531^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103693101 156250000 5877170723531 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2045721779/5000000000 : ℝ), (835349981/5000000000 : ℝ), (103693101/156250000 : ℝ)] ![(15698097866273/50000000000000 : ℝ), (4916048510153/50000000000000 : ℝ), (5877170723531/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2045721779/5000000000 : ℝ)|^35 ≤ (15698097866273/50000000000000 : ℝ)^27
        have hw : |(-2045721779/5000000000 : ℝ)|=(2045721779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(835349981/5000000000 : ℝ)|^35 ≤ (4916048510153/50000000000000 : ℝ)^27
        have hw : |(835349981/5000000000 : ℝ)|=(835349981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103693101/156250000 : ℝ)|^35 ≤ (5877170723531/10000000000000 : ℝ)^27
        have hw : |(103693101/156250000 : ℝ)|=(103693101/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5439393389/10000000000 : ℝ)*x 0 + (-3254665321/10000000000 : ℝ)*x 1 + (2038240467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5439393389/10000000000 : ℝ)^35 ≤ (5676819237331/12500000000000 : ℝ)^27 := by
    have hnat : (5439393389 : ℕ)^35*12500000000000^27 ≤ 5676819237331^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439393389 10000000000 5676819237331 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3254665321/10000000000 : ℝ)^35 ≤ (11669003599971/50000000000000 : ℝ)^27 := by
    have hnat : (3254665321 : ℕ)^35*50000000000000^27 ≤ 11669003599971^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3254665321 10000000000 11669003599971 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038240467/5000000000 : ℝ)^35 ≤ (15623719446001/50000000000000 : ℝ)^27 := by
    have hnat : (2038240467 : ℕ)^35*50000000000000^27 ≤ 15623719446001^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038240467 5000000000 15623719446001 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5439393389/10000000000 : ℝ), (-3254665321/10000000000 : ℝ), (2038240467/5000000000 : ℝ)] ![(5676819237331/12500000000000 : ℝ), (11669003599971/50000000000000 : ℝ), (15623719446001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5439393389/10000000000 : ℝ)|^35 ≤ (5676819237331/12500000000000 : ℝ)^27
        have hw : |(5439393389/10000000000 : ℝ)|=(5439393389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3254665321/10000000000 : ℝ)|^35 ≤ (11669003599971/50000000000000 : ℝ)^27
        have hw : |(-3254665321/10000000000 : ℝ)|=(3254665321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2038240467/5000000000 : ℝ)|^35 ≤ (15623719446001/50000000000000 : ℝ)^27
        have hw : |(2038240467/5000000000 : ℝ)|=(2038240467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (893561757/2000000000 : ℝ)*x 0 + (7072926139/10000000000 : ℝ)*x 1 + (-281727147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893561757/2000000000 : ℝ)^35 ≤ (35189970038607/100000000000000 : ℝ)^27 := by
    have hnat : (893561757 : ℕ)^35*100000000000000^27 ≤ 35189970038607^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893561757 2000000000 35189970038607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7072926139/10000000000 : ℝ)^35 ≤ (31915812451823/50000000000000 : ℝ)^27 := by
    have hnat : (7072926139 : ℕ)^35*50000000000000^27 ≤ 31915812451823^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7072926139 10000000000 31915812451823 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281727147/10000000000 : ℝ)^35 ≤ (978405041021/100000000000000 : ℝ)^27 := by
    have hnat : (281727147 : ℕ)^35*100000000000000^27 ≤ 978405041021^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281727147 10000000000 978405041021 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893561757/2000000000 : ℝ), (7072926139/10000000000 : ℝ), (-281727147/10000000000 : ℝ)] ![(35189970038607/100000000000000 : ℝ), (31915812451823/50000000000000 : ℝ), (978405041021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893561757/2000000000 : ℝ)|^35 ≤ (35189970038607/100000000000000 : ℝ)^27
        have hw : |(893561757/2000000000 : ℝ)|=(893561757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7072926139/10000000000 : ℝ)|^35 ≤ (31915812451823/50000000000000 : ℝ)^27
        have hw : |(7072926139/10000000000 : ℝ)|=(7072926139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281727147/10000000000 : ℝ)|^35 ≤ (978405041021/100000000000000 : ℝ)^27
        have hw : |(-281727147/10000000000 : ℝ)|=(281727147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (78949989/625000000 : ℝ)*x 0 + (1465144891/5000000000 : ℝ)*x 1 + (1956734237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78949989/625000000 : ℝ)^35 ≤ (342146072467/5000000000000 : ℝ)^27 := by
    have hnat : (78949989 : ℕ)^35*5000000000000^27 ≤ 342146072467^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78949989 625000000 342146072467 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1465144891/5000000000 : ℝ)^35 ≤ (20368457781569/100000000000000 : ℝ)^27 := by
    have hnat : (1465144891 : ℕ)^35*100000000000000^27 ≤ 20368457781569^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465144891 5000000000 20368457781569 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956734237/2500000000 : ℝ)^35 ≤ (36394310375701/50000000000000 : ℝ)^27 := by
    have hnat : (1956734237 : ℕ)^35*50000000000000^27 ≤ 36394310375701^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956734237 2500000000 36394310375701 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(78949989/625000000 : ℝ), (1465144891/5000000000 : ℝ), (1956734237/2500000000 : ℝ)] ![(342146072467/5000000000000 : ℝ), (20368457781569/100000000000000 : ℝ), (36394310375701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(78949989/625000000 : ℝ)|^35 ≤ (342146072467/5000000000000 : ℝ)^27
        have hw : |(78949989/625000000 : ℝ)|=(78949989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1465144891/5000000000 : ℝ)|^35 ≤ (20368457781569/100000000000000 : ℝ)^27
        have hw : |(1465144891/5000000000 : ℝ)|=(1465144891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1956734237/2500000000 : ℝ)|^35 ≤ (36394310375701/50000000000000 : ℝ)^27
        have hw : |(1956734237/2500000000 : ℝ)|=(1956734237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5371441989/10000000000 : ℝ)*x 0 + (1825316663/10000000000 : ℝ)*x 1 + (666923013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371441989/10000000000 : ℝ)^35 ≤ (44680478969841/100000000000000 : ℝ)^27 := by
    have hnat : (5371441989 : ℕ)^35*100000000000000^27 ≤ 44680478969841^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371441989 10000000000 44680478969841 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825316663/10000000000 : ℝ)^35 ≤ (11027459420673/100000000000000 : ℝ)^27 := by
    have hnat : (1825316663 : ℕ)^35*100000000000000^27 ≤ 11027459420673^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825316663 10000000000 11027459420673 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666923013/1250000000 : ℝ)^35 ≤ (692063462327/1562500000000 : ℝ)^27 := by
    have hnat : (666923013 : ℕ)^35*1562500000000^27 ≤ 692063462327^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666923013 1250000000 692063462327 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5371441989/10000000000 : ℝ), (1825316663/10000000000 : ℝ), (666923013/1250000000 : ℝ)] ![(44680478969841/100000000000000 : ℝ), (11027459420673/100000000000000 : ℝ), (692063462327/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5371441989/10000000000 : ℝ)|^35 ≤ (44680478969841/100000000000000 : ℝ)^27
        have hw : |(-5371441989/10000000000 : ℝ)|=(5371441989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1825316663/10000000000 : ℝ)|^35 ≤ (11027459420673/100000000000000 : ℝ)^27
        have hw : |(1825316663/10000000000 : ℝ)|=(1825316663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(666923013/1250000000 : ℝ)|^35 ≤ (692063462327/1562500000000 : ℝ)^27
        have hw : |(666923013/1250000000 : ℝ)|=(666923013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1864845933/5000000000 : ℝ)*x 0 + (-52402687/125000000 : ℝ)*x 1 + (4908320917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864845933/5000000000 : ℝ)^35 ≤ (27845898508169/100000000000000 : ℝ)^27 := by
    have hnat : (1864845933 : ℕ)^35*100000000000000^27 ≤ 27845898508169^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864845933 5000000000 27845898508169 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52402687/125000000 : ℝ)^35 ≤ (8100558680131/25000000000000 : ℝ)^27 := by
    have hnat : (52402687 : ℕ)^35*25000000000000^27 ≤ 8100558680131^27*125000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52402687 125000000 8100558680131 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4908320917/10000000000 : ℝ)^35 ≤ (39751866747967/100000000000000 : ℝ)^27 := by
    have hnat : (4908320917 : ℕ)^35*100000000000000^27 ≤ 39751866747967^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908320917 10000000000 39751866747967 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1864845933/5000000000 : ℝ), (-52402687/125000000 : ℝ), (4908320917/10000000000 : ℝ)] ![(27845898508169/100000000000000 : ℝ), (8100558680131/25000000000000 : ℝ), (39751866747967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1864845933/5000000000 : ℝ)|^35 ≤ (27845898508169/100000000000000 : ℝ)^27
        have hw : |(1864845933/5000000000 : ℝ)|=(1864845933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52402687/125000000 : ℝ)|^35 ≤ (8100558680131/25000000000000 : ℝ)^27
        have hw : |(-52402687/125000000 : ℝ)|=(52402687/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4908320917/10000000000 : ℝ)|^35 ≤ (39751866747967/100000000000000 : ℝ)^27
        have hw : |(4908320917/10000000000 : ℝ)|=(4908320917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4962955449/10000000000 : ℝ)*x 0 + (3189707411/5000000000 : ℝ)*x 1 + (-808046253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4962955449/10000000000 : ℝ)^35 ≤ (20163196451969/50000000000000 : ℝ)^27 := by
    have hnat : (4962955449 : ℕ)^35*50000000000000^27 ≤ 20163196451969^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4962955449 10000000000 20163196451969 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3189707411/5000000000 : ℝ)^35 ≤ (27919532007581/50000000000000 : ℝ)^27 := by
    have hnat : (3189707411 : ℕ)^35*50000000000000^27 ≤ 27919532007581^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189707411 5000000000 27919532007581 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808046253/10000000000 : ℝ)^35 ≤ (191727153189/5000000000000 : ℝ)^27 := by
    have hnat : (808046253 : ℕ)^35*5000000000000^27 ≤ 191727153189^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808046253 10000000000 191727153189 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4962955449/10000000000 : ℝ), (3189707411/5000000000 : ℝ), (-808046253/10000000000 : ℝ)] ![(20163196451969/50000000000000 : ℝ), (27919532007581/50000000000000 : ℝ), (191727153189/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4962955449/10000000000 : ℝ)|^35 ≤ (20163196451969/50000000000000 : ℝ)^27
        have hw : |(4962955449/10000000000 : ℝ)|=(4962955449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3189707411/5000000000 : ℝ)|^35 ≤ (27919532007581/50000000000000 : ℝ)^27
        have hw : |(3189707411/5000000000 : ℝ)|=(3189707411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-808046253/10000000000 : ℝ)|^35 ≤ (191727153189/5000000000000 : ℝ)^27
        have hw : |(-808046253/10000000000 : ℝ)|=(808046253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s0_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1120210343/10000000000 : ℝ)*x 0 + (4762810539/10000000000 : ℝ)*x 1 + (3192960389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120210343/10000000000 : ℝ)^35 ≤ (5856128049221/100000000000000 : ℝ)^27 := by
    have hnat : (1120210343 : ℕ)^35*100000000000000^27 ≤ 5856128049221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120210343 10000000000 5856128049221 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4762810539/10000000000 : ℝ)^35 ≤ (38230976996541/100000000000000 : ℝ)^27 := by
    have hnat : (4762810539 : ℕ)^35*100000000000000^27 ≤ 38230976996541^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762810539 10000000000 38230976996541 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192960389/5000000000 : ℝ)^35 ≤ (13978223733969/25000000000000 : ℝ)^27 := by
    have hnat : (3192960389 : ℕ)^35*25000000000000^27 ≤ 13978223733969^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192960389 5000000000 13978223733969 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120210343/10000000000 : ℝ), (4762810539/10000000000 : ℝ), (3192960389/5000000000 : ℝ)] ![(5856128049221/100000000000000 : ℝ), (38230976996541/100000000000000 : ℝ), (13978223733969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120210343/10000000000 : ℝ)|^35 ≤ (5856128049221/100000000000000 : ℝ)^27
        have hw : |(1120210343/10000000000 : ℝ)|=(1120210343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4762810539/10000000000 : ℝ)|^35 ≤ (38230976996541/100000000000000 : ℝ)^27
        have hw : |(4762810539/10000000000 : ℝ)|=(4762810539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192960389/5000000000 : ℝ)|^35 ≤ (13978223733969/25000000000000 : ℝ)^27
        have hw : |(3192960389/5000000000 : ℝ)|=(3192960389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-550486613/1250000000 : ℝ)*x 0 + (3519816293/10000000000 : ℝ)*x 1 + (153020291/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550486613/1250000000 : ℝ)^35 ≤ (8634693087813/25000000000000 : ℝ)^27 := by
    have hnat : (550486613 : ℕ)^35*25000000000000^27 ≤ 8634693087813^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550486613 1250000000 8634693087813 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3519816293/10000000000 : ℝ)^35 ≤ (6457963122571/25000000000000 : ℝ)^27 := by
    have hnat : (3519816293 : ℕ)^35*25000000000000^27 ≤ 6457963122571^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3519816293 10000000000 6457963122571 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153020291/312500000 : ℝ)^35 ≤ (39629375141151/100000000000000 : ℝ)^27 := by
    have hnat : (153020291 : ℕ)^35*100000000000000^27 ≤ 39629375141151^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153020291 312500000 39629375141151 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550486613/1250000000 : ℝ), (3519816293/10000000000 : ℝ), (153020291/312500000 : ℝ)] ![(8634693087813/25000000000000 : ℝ), (6457963122571/25000000000000 : ℝ), (39629375141151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550486613/1250000000 : ℝ)|^35 ≤ (8634693087813/25000000000000 : ℝ)^27
        have hw : |(-550486613/1250000000 : ℝ)|=(550486613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3519816293/10000000000 : ℝ)|^35 ≤ (6457963122571/25000000000000 : ℝ)^27
        have hw : |(3519816293/10000000000 : ℝ)|=(3519816293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153020291/312500000 : ℝ)|^35 ≤ (39629375141151/100000000000000 : ℝ)^27
        have hw : |(153020291/312500000 : ℝ)|=(153020291/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (906766527/2000000000 : ℝ)*x 0 + (-3623670767/10000000000 : ℝ)*x 1 + (934816507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (906766527/2000000000 : ℝ)^35 ≤ (35865548713667/100000000000000 : ℝ)^27 := by
    have hnat : (906766527 : ℕ)^35*100000000000000^27 ≤ 35865548713667^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906766527 2000000000 35865548713667 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3623670767/10000000000 : ℝ)^35 ≤ (13412080115983/50000000000000 : ℝ)^27 := by
    have hnat : (3623670767 : ℕ)^35*50000000000000^27 ≤ 13412080115983^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623670767 10000000000 13412080115983 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934816507/2000000000 : ℝ)^35 ≤ (7462058207009/20000000000000 : ℝ)^27 := by
    have hnat : (934816507 : ℕ)^35*20000000000000^27 ≤ 7462058207009^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934816507 2000000000 7462058207009 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(906766527/2000000000 : ℝ), (-3623670767/10000000000 : ℝ), (934816507/2000000000 : ℝ)] ![(35865548713667/100000000000000 : ℝ), (13412080115983/50000000000000 : ℝ), (7462058207009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(906766527/2000000000 : ℝ)|^35 ≤ (35865548713667/100000000000000 : ℝ)^27
        have hw : |(906766527/2000000000 : ℝ)|=(906766527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3623670767/10000000000 : ℝ)|^35 ≤ (13412080115983/50000000000000 : ℝ)^27
        have hw : |(-3623670767/10000000000 : ℝ)|=(3623670767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934816507/2000000000 : ℝ)|^35 ≤ (7462058207009/20000000000000 : ℝ)^27
        have hw : |(934816507/2000000000 : ℝ)|=(934816507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (870620249/2000000000 : ℝ)*x 0 + (2848606999/5000000000 : ℝ)*x 1 + (-2635452391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870620249/2000000000 : ℝ)^35 ≤ (34023280130617/100000000000000 : ℝ)^27 := by
    have hnat : (870620249 : ℕ)^35*100000000000000^27 ≤ 34023280130617^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870620249 2000000000 34023280130617 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848606999/5000000000 : ℝ)^35 ≤ (24112167416811/50000000000000 : ℝ)^27 := by
    have hnat : (2848606999 : ℕ)^35*50000000000000^27 ≤ 24112167416811^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848606999 5000000000 24112167416811 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635452391/10000000000 : ℝ)^35 ≤ (710095400947/4000000000000 : ℝ)^27 := by
    have hnat : (2635452391 : ℕ)^35*4000000000000^27 ≤ 710095400947^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635452391 10000000000 710095400947 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870620249/2000000000 : ℝ), (2848606999/5000000000 : ℝ), (-2635452391/10000000000 : ℝ)] ![(34023280130617/100000000000000 : ℝ), (24112167416811/50000000000000 : ℝ), (710095400947/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870620249/2000000000 : ℝ)|^35 ≤ (34023280130617/100000000000000 : ℝ)^27
        have hw : |(870620249/2000000000 : ℝ)|=(870620249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848606999/5000000000 : ℝ)|^35 ≤ (24112167416811/50000000000000 : ℝ)^27
        have hw : |(2848606999/5000000000 : ℝ)|=(2848606999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2635452391/10000000000 : ℝ)|^35 ≤ (710095400947/4000000000000 : ℝ)^27
        have hw : |(-2635452391/10000000000 : ℝ)|=(2635452391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309081_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3148062319/10000000000 : ℝ)*x 0 + (412009363/1000000000 : ℝ)*x 1 + (5490326599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3148062319/10000000000 : ℝ)^35 ≤ (22351949943843/100000000000000 : ℝ)^27 := by
    have hnat : (3148062319 : ℕ)^35*100000000000000^27 ≤ 22351949943843^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3148062319 10000000000 22351949943843 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412009363/1000000000 : ℝ)^35 ≤ (3168148144827/10000000000000 : ℝ)^27 := by
    have hnat : (412009363 : ℕ)^35*10000000000000^27 ≤ 3168148144827^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412009363 1000000000 3168148144827 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490326599/10000000000 : ℝ)^35 ≤ (45966568597149/100000000000000 : ℝ)^27 := by
    have hnat : (5490326599 : ℕ)^35*100000000000000^27 ≤ 45966568597149^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490326599 10000000000 45966568597149 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3148062319/10000000000 : ℝ), (412009363/1000000000 : ℝ), (5490326599/10000000000 : ℝ)] ![(22351949943843/100000000000000 : ℝ), (3168148144827/10000000000000 : ℝ), (45966568597149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3148062319/10000000000 : ℝ)|^35 ≤ (22351949943843/100000000000000 : ℝ)^27
        have hw : |(3148062319/10000000000 : ℝ)|=(3148062319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412009363/1000000000 : ℝ)|^35 ≤ (3168148144827/10000000000000 : ℝ)^27
        have hw : |(412009363/1000000000 : ℝ)|=(412009363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490326599/10000000000 : ℝ)|^35 ≤ (45966568597149/100000000000000 : ℝ)^27
        have hw : |(5490326599/10000000000 : ℝ)|=(5490326599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309081 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4465721483/10000000000 : ℝ)*X 0 0+(2713481643/10000000000 : ℝ)*X 0 1+(5529728329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1014090009/2500000000 : ℝ)*X 2 0+(701314741/1000000000 : ℝ)*X 2 1+(-139344317/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1222676129/2500000000 : ℝ)*X 0 0+(345412323/2000000000 : ℝ)*X 0 1+(5873620787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4800795167/10000000000 : ℝ)*X 1 0+(-302307713/1250000000 : ℝ)*X 1 1+(2723277653/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1540766973/5000000000 : ℝ)*X 2 0+(4038355559/5000000000 : ℝ)*X 2 1+(-285488717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((687955337/5000000000 : ℝ)*X 0 0+(5144550851/10000000000 : ℝ)*X 0 1+(1173588533/2000000000 : ℝ)*X 0 2+(687955337/5000000000 : ℝ)*X 1 0+(5144550851/10000000000 : ℝ)*X 1 1+(1173588533/2000000000 : ℝ)*X 1 2+(687955337/5000000000 : ℝ)*X 2 0+(5144550851/10000000000 : ℝ)*X 2 1+(1173588533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2045721779/5000000000 : ℝ)*X 0 0+(835349981/5000000000 : ℝ)*X 0 1+(103693101/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5439393389/10000000000 : ℝ)*X 1 0+(-3254665321/10000000000 : ℝ)*X 1 1+(2038240467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((893561757/2000000000 : ℝ)*X 2 0+(7072926139/10000000000 : ℝ)*X 2 1+(-281727147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((78949989/625000000 : ℝ)*X 0 0+(1465144891/5000000000 : ℝ)*X 0 1+(1956734237/2500000000 : ℝ)*X 0 2+(78949989/625000000 : ℝ)*X 1 0+(1465144891/5000000000 : ℝ)*X 1 1+(1956734237/2500000000 : ℝ)*X 1 2+(78949989/625000000 : ℝ)*X 2 0+(1465144891/5000000000 : ℝ)*X 2 1+(1956734237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5371441989/10000000000 : ℝ)*X 0 0+(1825316663/10000000000 : ℝ)*X 0 1+(666923013/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1864845933/5000000000 : ℝ)*X 1 0+(-52402687/125000000 : ℝ)*X 1 1+(4908320917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4962955449/10000000000 : ℝ)*X 2 0+(3189707411/5000000000 : ℝ)*X 2 1+(-808046253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1120210343/10000000000 : ℝ)*X 0 0+(4762810539/10000000000 : ℝ)*X 0 1+(3192960389/5000000000 : ℝ)*X 0 2+(1120210343/10000000000 : ℝ)*X 1 0+(4762810539/10000000000 : ℝ)*X 1 1+(3192960389/5000000000 : ℝ)*X 1 2+(1120210343/10000000000 : ℝ)*X 2 0+(4762810539/10000000000 : ℝ)*X 2 1+(3192960389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((15679/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15679/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20393860570345452562293/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1146539833317/1000000000000 : ℝ)*(base49) + (315569436567/250000000000 : ℝ)*(base59) + (1946692463311/500000000000 : ℝ)*(major_s0_0) + (1946692463311/500000000000 : ℝ)*(major_s0_1) + (1946692463311/500000000000 : ℝ)*(major_s0_2) + (9822499/125000000000 : ℝ)*(sp_s0_0) + (10832649/250000000000 : ℝ)*(sp_s0_2) + (5341789374179/1000000000000 : ℝ)*(sp_s0_7) + (213675364099/40000000000 : ℝ)*(sp_s0_8) + (2670926023309/500000000000 : ℝ)*(sp_s0_9) + (2444829675677/1000000000000 : ℝ)*(sp_s0_13) + (27423043/1000000000000 : ℝ)*(sp_s0_14) + (11274739/1000000000000 : ℝ)*(sp_s0_22) + (2630073/62500000000 : ℝ)*(sp_s0_27) + (488974351369/200000000000 : ℝ)*(f.failure) + (2670947688607/500000000000 : ℝ)*(f.sum) + (1382039346940071/5000000000000000000000000000 : ℝ)*base63 + (237358085686249/5000000000000000000000000000 : ℝ)*base65 + (1302241766626911/2500000000000000000000000000 : ℝ)*base66 + (492961814123089/2500000000000000000000000000 : ℝ)*base68 + (1118909176932427/5000000000000000000000000000 : ℝ)*base71 + (2502106539686249/5000000000000000000000000000 : ℝ)*base72 + (364747075686249/5000000000000000000000000000 : ℝ)*base75 + (1109074231876911/2500000000000000000000000000 : ℝ)*base76 + (1753637181440071/5000000000000000000000000000 : ℝ)*base78 + (19143/20000000000000000 : ℝ)*base87 + (19143/20000000000000000 : ℝ)*base89 + (19143/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((18643/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(18643/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17967071257422680666067/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57069604659/200000000000 : ℝ)*(base40) + (42145302759/50000000000 : ℝ)*(base49) + (1695930436427/1000000000000 : ℝ)*(base59) + (1096217/250000000000 : ℝ)*(base60) + (4392409297309/1000000000000 : ℝ)*(major_s0_0) + (4392409297309/1000000000000 : ℝ)*(major_s0_1) + (4392409297309/1000000000000 : ℝ)*(major_s0_2) + (51913551/1000000000000 : ℝ)*(sp_s0_7) + (812099/31250000000 : ℝ)*(sp_s0_8) + (3013262563631/500000000000 : ℝ)*(sp_s0_14) + (1205310210729/200000000000 : ℝ)*(sp_s0_15) + (753312061099/125000000000 : ℝ)*(sp_s0_16) + (1379118381291/500000000000 : ℝ)*(sp_s0_20) + (80552021/1000000000000 : ℝ)*(sp_s0_23) + (1379118381291/500000000000 : ℝ)*(f.failure) + (6026577040813/1000000000000 : ℝ)*(f.sum) + (3130718417740251/10000000000000000000000000000 : ℝ)*base62 + (5348807022568331/10000000000000000000000000000 : ℝ)*base65 + (1863575238154291/5000000000000000000000000000 : ℝ)*base67 + (1566892026845709/5000000000000000000000000000 : ℝ)*base69 + (5061635665876913/10000000000000000000000000000 : ℝ)*base71 + (214050629568331/10000000000000000000000000000 : ℝ)*base72 + (4028617338568331/10000000000000000000000000000 : ℝ)*base75 + (4328466971654291/5000000000000000000000000000 : ℝ)*base77 + (4555508637259749/10000000000000000000000000000 : ℝ)*base78 + (2123/50000000000000000 : ℝ)*base86 + (2123/50000000000000000 : ℝ)*base88 + (2123/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16967/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16967/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19489338565613677395291/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2461201/500000000000 : ℝ)*(base40) + (545849130449/1000000000000 : ℝ)*(base49) + (687115604679/500000000000 : ℝ)*(base59) + (4105852302103/1000000000000 : ℝ)*(major_s0_0) + (4105852302103/1000000000000 : ℝ)*(major_s0_1) + (4105852302103/1000000000000 : ℝ)*(major_s0_2) + (2739147/50000000000 : ℝ)*(sp_s0_0) + (139941653/1000000000000 : ℝ)*(sp_s0_13) + (12611823/200000000000 : ℝ)*(sp_s0_15) + (25324427/500000000000 : ℝ)*(sp_s0_16) + (1408338212407/250000000000 : ℝ)*(sp_s0_21) + (1408336143363/250000000000 : ℝ)*(sp_s0_22) + (2816678491857/500000000000 : ℝ)*(sp_s0_23) + (103126073313/40000000000 : ℝ)*(sp_s0_27) + (1289145887239/500000000000 : ℝ)*(f.failure) + (704175954071/125000000000 : ℝ)*(f.sum) + (3287942313769583/10000000000000000000000000000 : ℝ)*base63 + (2830404625199777/10000000000000000000000000000 : ℝ)*base65 + (477471589284903/5000000000000000000000000000 : ℝ)*base66 + (1837657123784903/5000000000000000000000000000 : ℝ)*base69 + (709840267370029/10000000000000000000000000000 : ℝ)*base70 + (4394462223800223/10000000000000000000000000000 : ℝ)*base73 + (975612714199777/10000000000000000000000000000 : ℝ)*base75 + (968551251784903/5000000000000000000000000000 : ℝ)*base76 + (759074786230417/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (967/50000000000000000 : ℝ)*base86 + (967/50000000000000000 : ℝ)*base88 + (967/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (15679/50000 : ℝ) ^ (69/16 : ℝ) ≤ (134596039198963699/20000000000000000000 : ℝ) := by
    have hpowers : (15679/50000 : ℝ)^69 ≤ (134596039198963699/20000000000000000000 : ℝ)^16 := by
      have hnat : (15679 : ℕ)^69*20000000000000000000^16 ≤ 134596039198963699^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15679 50000 134596039198963699 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15679/50000 : ℝ)) (X := (134596039198963699/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20134596039198963699/20000000000000000000 : ℝ) ≤ (5007782581514009/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (20134596039198963699/20000000000000000000 : ℝ)^16 ≤ (5007782581514009/5000000000000000 : ℝ)^69 := by
      have hnat : (20134596039198963699 : ℕ)^16*5000000000000000^69 ≤ 5007782581514009^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20134596039198963699 20000000000000000000 5007782581514009 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007782581514009/5000000000000000 : ℝ)) (X := (20134596039198963699/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10134596039198963699/10000000000000000000 : ℝ) ≤ (5015525303718607/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10134596039198963699/10000000000000000000 : ℝ)^16 ≤ (5015525303718607/5000000000000000 : ℝ)^69 := by
      have hnat : (10134596039198963699 : ℕ)^16*5000000000000000^69 ≤ 5015525303718607^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10134596039198963699 10000000000000000000 5015525303718607 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015525303718607/5000000000000000 : ℝ)) (X := (10134596039198963699/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7782581514009/1567900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3871361102299/783950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (15679/50000 : ℝ)) (alpha := (7782581514009/1567900000000000 : ℝ)) (beta := (3871361102299/783950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15679/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7782581514009/1567900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3871361102299/783950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18643/50000 : ℝ) ^ (69/16 : ℝ) ≤ (1420009474171855987/100000000000000000000 : ℝ) := by
    have hpowers : (18643/50000 : ℝ)^69 ≤ (1420009474171855987/100000000000000000000 : ℝ)^16 := by
      have hnat : (18643 : ℕ)^69*100000000000000000000^16 ≤ 1420009474171855987^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18643 50000 1420009474171855987 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18643/50000 : ℝ)) (X := (1420009474171855987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (101420009474171855987/100000000000000000000 : ℝ) ≤ (10032749667441683/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (101420009474171855987/100000000000000000000 : ℝ)^16 ≤ (10032749667441683/10000000000000000 : ℝ)^69 := by
      have hnat : (101420009474171855987 : ℕ)^16*10000000000000000^69 ≤ 10032749667441683^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101420009474171855987 100000000000000000000 10032749667441683 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032749667441683/10000000000000000 : ℝ)) (X := (101420009474171855987/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (51420009474171855987/50000000000000000000 : ℝ) ≤ (10065148996626977/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (51420009474171855987/50000000000000000000 : ℝ)^16 ≤ (10065148996626977/10000000000000000 : ℝ)^69 := by
      have hnat : (51420009474171855987 : ℕ)^16*10000000000000000^69 ≤ 10065148996626977^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51420009474171855987 50000000000000000000 10065148996626977 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10065148996626977/10000000000000000 : ℝ)) (X := (51420009474171855987/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(32749667441683/3728600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(16199664592647/1864300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (18643/50000 : ℝ)) (alpha := (32749667441683/3728600000000000 : ℝ)) (beta := (16199664592647/1864300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (18643/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(32749667441683/3728600000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(16199664592647/1864300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16967/100000 : ℝ) ^ (69/16 : ℝ) ≤ (11901777561181939/25000000000000000000 : ℝ) := by
    have hpowers : (16967/100000 : ℝ)^69 ≤ (11901777561181939/25000000000000000000 : ℝ)^16 := by
      have hnat : (16967 : ℕ)^69*25000000000000000000^16 ≤ 11901777561181939^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16967 100000 11901777561181939 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16967/100000 : ℝ)) (X := (11901777561181939/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25011901777561181939/25000000000000000000 : ℝ) ≤ (5000551865602951/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25011901777561181939/25000000000000000000 : ℝ)^16 ≤ (5000551865602951/5000000000000000 : ℝ)^69 := by
      have hnat : (25011901777561181939 : ℕ)^16*5000000000000000^69 ≤ 5000551865602951^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011901777561181939 25000000000000000000 5000551865602951 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000551865602951/5000000000000000 : ℝ)) (X := (25011901777561181939/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12511901777561181939/12500000000000000000 : ℝ) ≤ (10002207059067551/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (12511901777561181939/12500000000000000000 : ℝ)^16 ≤ (10002207059067551/10000000000000000 : ℝ)^69 := by
      have hnat : (12511901777561181939 : ℕ)^16*10000000000000000^69 ≤ 10002207059067551^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511901777561181939 12500000000000000000 10002207059067551 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002207059067551/10000000000000000 : ℝ)) (X := (12511901777561181939/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(551865602951/848350000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1103327861649/1696700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (16967/100000 : ℝ)) (alpha := (551865602951/848350000000000 : ℝ)) (beta := (1103327861649/1696700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16967/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(551865602951/848350000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1103327861649/1696700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-550486613/1250000000 : ℝ)*X 0 0+(3519816293/10000000000 : ℝ)*X 0 1+(153020291/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((906766527/2000000000 : ℝ)*X 1 0+(-3623670767/10000000000 : ℝ)*X 1 1+(934816507/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((870620249/2000000000 : ℝ)*X 2 0+(2848606999/5000000000 : ℝ)*X 2 1+(-2635452391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3148062319/10000000000 : ℝ)*X 0 0+(412009363/1000000000 : ℝ)*X 0 1+(5490326599/10000000000 : ℝ)*X 0 2+(3148062319/10000000000 : ℝ)*X 1 0+(412009363/1000000000 : ℝ)*X 1 1+(5490326599/10000000000 : ℝ)*X 1 2+(3148062319/10000000000 : ℝ)*X 2 0+(412009363/1000000000 : ℝ)*X 2 1+(5490326599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309081_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-3119417386931256232448194677494337/481506323330000000000000000000000 : ℝ) := by norm_num
    linear_combination (2811/8000000000 : ℝ)*(base13) + (1171/125000000000 : ℝ)*(base16) + (226323/200000000000 : ℝ)*(base23) + (20970089053/500000000000 : ℝ)*(base40) + (3237808517/10000000000 : ℝ)*(base49) + (358439772143/500000000000 : ℝ)*(base59) + (148776690641/500000000000 : ℝ)*(base60) + (111297/500000000000 : ℝ)*(ratio_s0_1) + (159247/100000 : ℝ)*(major_s1_0) + (159247/100000 : ℝ)*(major_s1_1) + (159247/100000 : ℝ)*(major_s1_2) + (2159484883319/1000000000000 : ℝ)*(sp_s1_0) + (1079742612663/500000000000 : ℝ)*(sp_s1_1) + (2159484103079/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1079742617347/500000000000 : ℝ)*(f.sum) + (59730524966855207/395394726250000000000000000000 : ℝ)*base63 + (37666236295589/169670000000000000000000000 : ℝ)*base64 + (68629888461/2912968750000000000000000 : ℝ)*base66 + (346967080767/16967000000000000000000000 : ℝ)*base68 + (370263044945320047/1330127965000000000000000000000 : ℝ)*base70 + (4580119022739/15679000000000000000000000 : ℝ)*base72 + (13618842312547/37286000000000000000000000 : ℝ)*base75 + (12582743388641/78395000000000000000000000 : ℝ)*base77 + (566444012878035267/2923035970000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c309084_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108580639/5000000000 : ℝ)*x 0 + (-130418951/250000000 : ℝ)*x 1 + (672130069/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108580639/5000000000 : ℝ)^35 ≤ (16326199217399/50000000000000 : ℝ)^27 := by
    have hnat : (2108580639 : ℕ)^35*50000000000000^27 ≤ 16326199217399^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108580639 5000000000 16326199217399 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130418951/250000000 : ℝ)^35 ≤ (43019718708921/100000000000000 : ℝ)^27 := by
    have hnat : (130418951 : ℕ)^35*100000000000000^27 ≤ 43019718708921^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130418951 250000000 43019718708921 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672130069/2000000000 : ℝ)^35 ≤ (12163941418067/50000000000000 : ℝ)^27 := by
    have hnat : (672130069 : ℕ)^35*50000000000000^27 ≤ 12163941418067^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672130069 2000000000 12163941418067 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108580639/5000000000 : ℝ), (-130418951/250000000 : ℝ), (672130069/2000000000 : ℝ)] ![(16326199217399/50000000000000 : ℝ), (43019718708921/100000000000000 : ℝ), (12163941418067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108580639/5000000000 : ℝ)|^35 ≤ (16326199217399/50000000000000 : ℝ)^27
        have hw : |(-2108580639/5000000000 : ℝ)|=(2108580639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130418951/250000000 : ℝ)|^35 ≤ (43019718708921/100000000000000 : ℝ)^27
        have hw : |(-130418951/250000000 : ℝ)|=(130418951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672130069/2000000000 : ℝ)|^35 ≤ (12163941418067/50000000000000 : ℝ)^27
        have hw : |(672130069/2000000000 : ℝ)|=(672130069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309084_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (672130069/2000000000 : ℝ)*x 0 + (2108580639/5000000000 : ℝ)*x 1 + (130418951/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672130069/2000000000 : ℝ)^35 ≤ (12163941418067/50000000000000 : ℝ)^27 := by
    have hnat : (672130069 : ℕ)^35*50000000000000^27 ≤ 12163941418067^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672130069 2000000000 12163941418067 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108580639/5000000000 : ℝ)^35 ≤ (16326199217399/50000000000000 : ℝ)^27 := by
    have hnat : (2108580639 : ℕ)^35*50000000000000^27 ≤ 16326199217399^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108580639 5000000000 16326199217399 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130418951/250000000 : ℝ)^35 ≤ (43019718708921/100000000000000 : ℝ)^27 := by
    have hnat : (130418951 : ℕ)^35*100000000000000^27 ≤ 43019718708921^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130418951 250000000 43019718708921 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672130069/2000000000 : ℝ), (2108580639/5000000000 : ℝ), (130418951/250000000 : ℝ)] ![(12163941418067/50000000000000 : ℝ), (16326199217399/50000000000000 : ℝ), (43019718708921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672130069/2000000000 : ℝ)|^35 ≤ (12163941418067/50000000000000 : ℝ)^27
        have hw : |(672130069/2000000000 : ℝ)|=(672130069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2108580639/5000000000 : ℝ)|^35 ≤ (16326199217399/50000000000000 : ℝ)^27
        have hw : |(2108580639/5000000000 : ℝ)|=(2108580639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130418951/250000000 : ℝ)|^35 ≤ (43019718708921/100000000000000 : ℝ)^27
        have hw : |(130418951/250000000 : ℝ)|=(130418951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309084_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (130418951/250000000 : ℝ)*x 0 + (-672130069/2000000000 : ℝ)*x 1 + (-2108580639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130418951/250000000 : ℝ)^35 ≤ (43019718708921/100000000000000 : ℝ)^27 := by
    have hnat : (130418951 : ℕ)^35*100000000000000^27 ≤ 43019718708921^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130418951 250000000 43019718708921 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672130069/2000000000 : ℝ)^35 ≤ (12163941418067/50000000000000 : ℝ)^27 := by
    have hnat : (672130069 : ℕ)^35*50000000000000^27 ≤ 12163941418067^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672130069 2000000000 12163941418067 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108580639/5000000000 : ℝ)^35 ≤ (16326199217399/50000000000000 : ℝ)^27 := by
    have hnat : (2108580639 : ℕ)^35*50000000000000^27 ≤ 16326199217399^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108580639 5000000000 16326199217399 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130418951/250000000 : ℝ), (-672130069/2000000000 : ℝ), (-2108580639/5000000000 : ℝ)] ![(43019718708921/100000000000000 : ℝ), (12163941418067/50000000000000 : ℝ), (16326199217399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130418951/250000000 : ℝ)|^35 ≤ (43019718708921/100000000000000 : ℝ)^27
        have hw : |(130418951/250000000 : ℝ)|=(130418951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-672130069/2000000000 : ℝ)|^35 ≤ (12163941418067/50000000000000 : ℝ)^27
        have hw : |(-672130069/2000000000 : ℝ)|=(672130069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108580639/5000000000 : ℝ)|^35 ≤ (16326199217399/50000000000000 : ℝ)^27
        have hw : |(-2108580639/5000000000 : ℝ)|=(2108580639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309084_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (535605521/1250000000 : ℝ)*x 0 + (-535605521/1250000000 : ℝ)*x 1 + (535605521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535605521/1250000000 : ℝ)^35 ≤ (16666666665249/50000000000000 : ℝ)^27 := by
    have hnat : (535605521 : ℕ)^35*50000000000000^27 ≤ 16666666665249^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535605521 1250000000 16666666665249 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535605521/1250000000 : ℝ), (-535605521/1250000000 : ℝ), (535605521/1250000000 : ℝ)] ![(16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ), (16666666665249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(-535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(535605521/1250000000 : ℝ)|^35 ≤ (16666666665249/50000000000000 : ℝ)^27
        have hw : |(535605521/1250000000 : ℝ)|=(535605521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309084 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2108580639/5000000000 : ℝ)*X 0 0+(-130418951/250000000 : ℝ)*X 0 1+(672130069/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((672130069/2000000000 : ℝ)*X 1 0+(2108580639/5000000000 : ℝ)*X 1 1+(130418951/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((130418951/250000000 : ℝ)*X 2 0+(-672130069/2000000000 : ℝ)*X 2 1+(-2108580639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((535605521/1250000000 : ℝ)*X 0 0+(-535605521/1250000000 : ℝ)*X 0 1+(535605521/1250000000 : ℝ)*X 0 2+(535605521/1250000000 : ℝ)*X 1 0+(-535605521/1250000000 : ℝ)*X 1 1+(535605521/1250000000 : ℝ)*X 1 2+(535605521/1250000000 : ℝ)*X 2 0+(-535605521/1250000000 : ℝ)*X 2 1+(535605521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309084_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-64678713326331270385733/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (999999991711/1000000000000 : ℝ)*(base6) + (119557840779/250000000000 : ℝ)*(base40) + (119557840779/250000000000 : ℝ)*(base50) + (119557840779/250000000000 : ℝ)*(base60) + (159247/100000 : ℝ)*(major_s0_0) + (159247/100000 : ℝ)*(major_s0_1) + (159247/100000 : ℝ)*(major_s0_2) + (2489290441443/1000000000000 : ℝ)*(sp_s0_0) + (2489290441443/1000000000000 : ℝ)*(sp_s0_1) + (2489290441443/1000000000000 : ℝ)*(sp_s0_2) + (8289/1000000000000 : ℝ)*(sp_s0_6) + (2489290441443/1000000000000 : ℝ)*(f.sum) + (2156096047/2500000000000000000000 : ℝ)*base62 + (2024304501/5000000000000000000000 : ℝ)*base65 + (4134827447/10000000000000000000000 : ℝ)*base66 + (4134827447/10000000000000000000000 : ℝ)*base68 + (2156096047/2500000000000000000000 : ℝ)*base71 + (2024304501/5000000000000000000000 : ℝ)*base72 + (2024304501/5000000000000000000000 : ℝ)*base74 + (4134827447/10000000000000000000000 : ℝ)*base77 + (2156096047/2500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p009_b037 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=81 ∨ c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c309081 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309082 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b037 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
