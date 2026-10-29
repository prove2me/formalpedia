-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:41.977075+00:00
-- url     : https://prove2.me/submissions/807029fd-17a8-4c4c-b16d-62be5faa1142

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307062_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307062_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307062_s4
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c307062 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c307062_s0 p hpa hpb X hX
  have h1 := collision_c307062_s1 p hpa hpb X hX h0
  have h2 := collision_c307062_s2 p hpa hpb X hX h1
  have h3 := collision_c307062_s3 p hpa hpb X hX h2
  exact collision_c307062_s4 p hpa hpb X hX h3

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
theorem collision_support_c307064_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-404327261/1250000000 : ℝ)*x 0 + (-3762221747/10000000000 : ℝ)*x 1 + (-5822156573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404327261/1250000000 : ℝ)^17 ≤ (11427976171049/50000000000000 : ℝ)^13 := by
    have hnat : (404327261 : ℕ)^17*50000000000000^13 ≤ 11427976171049^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404327261 1250000000 11427976171049 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3762221747/10000000000 : ℝ)^17 ≤ (13924573383119/50000000000000 : ℝ)^13 := by
    have hnat : (3762221747 : ℕ)^17*50000000000000^13 ≤ 13924573383119^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762221747 10000000000 13924573383119 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5822156573/10000000000 : ℝ)^17 ≤ (4929490087791/10000000000000 : ℝ)^13 := by
    have hnat : (5822156573 : ℕ)^17*10000000000000^13 ≤ 4929490087791^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5822156573 10000000000 4929490087791 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404327261/1250000000 : ℝ), (-3762221747/10000000000 : ℝ), (-5822156573/10000000000 : ℝ)] ![(11427976171049/50000000000000 : ℝ), (13924573383119/50000000000000 : ℝ), (4929490087791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404327261/1250000000 : ℝ)|^17 ≤ (11427976171049/50000000000000 : ℝ)^13
        have hw : |(-404327261/1250000000 : ℝ)|=(404327261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3762221747/10000000000 : ℝ)|^17 ≤ (13924573383119/50000000000000 : ℝ)^13
        have hw : |(-3762221747/10000000000 : ℝ)|=(3762221747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5822156573/10000000000 : ℝ)|^17 ≤ (4929490087791/10000000000000 : ℝ)^13
        have hw : |(-5822156573/10000000000 : ℝ)|=(5822156573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3471811209/10000000000 : ℝ)*x 0 + (5639811963/10000000000 : ℝ)*x 1 + (-1870413177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3471811209/10000000000 : ℝ)^17 ≤ (25071986624107/100000000000000 : ℝ)^13 := by
    have hnat : (3471811209 : ℕ)^17*100000000000000^13 ≤ 25071986624107^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3471811209 10000000000 25071986624107 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639811963/10000000000 : ℝ)^17 ≤ (23642895736749/50000000000000 : ℝ)^13 := by
    have hnat : (5639811963 : ℕ)^17*50000000000000^13 ≤ 23642895736749^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639811963 10000000000 23642895736749 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870413177/5000000000 : ℝ)^17 ≤ (6910555472123/25000000000000 : ℝ)^13 := by
    have hnat : (1870413177 : ℕ)^17*25000000000000^13 ≤ 6910555472123^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870413177 5000000000 6910555472123 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3471811209/10000000000 : ℝ), (5639811963/10000000000 : ℝ), (-1870413177/5000000000 : ℝ)] ![(25071986624107/100000000000000 : ℝ), (23642895736749/50000000000000 : ℝ), (6910555472123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3471811209/10000000000 : ℝ)|^17 ≤ (25071986624107/100000000000000 : ℝ)^13
        have hw : |(3471811209/10000000000 : ℝ)|=(3471811209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5639811963/10000000000 : ℝ)|^17 ≤ (23642895736749/50000000000000 : ℝ)^13
        have hw : |(5639811963/10000000000 : ℝ)|=(5639811963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870413177/5000000000 : ℝ)|^17 ≤ (6910555472123/25000000000000 : ℝ)^13
        have hw : |(-1870413177/5000000000 : ℝ)|=(1870413177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1647772653/2500000000 : ℝ)*x 0 + (-3624160201/10000000000 : ℝ)*x 1 + (2403866313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1647772653/2500000000 : ℝ)^17 ≤ (14494119554023/25000000000000 : ℝ)^13 := by
    have hnat : (1647772653 : ℕ)^17*25000000000000^13 ≤ 14494119554023^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647772653 2500000000 14494119554023 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3624160201/10000000000 : ℝ)^17 ≤ (26520327962703/100000000000000 : ℝ)^13 := by
    have hnat : (3624160201 : ℕ)^17*100000000000000^13 ≤ 26520327962703^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624160201 10000000000 26520327962703 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2403866313/10000000000 : ℝ)^17 ≤ (1550319381679/10000000000000 : ℝ)^13 := by
    have hnat : (2403866313 : ℕ)^17*10000000000000^13 ≤ 1550319381679^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403866313 10000000000 1550319381679 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1647772653/2500000000 : ℝ), (-3624160201/10000000000 : ℝ), (2403866313/10000000000 : ℝ)] ![(14494119554023/25000000000000 : ℝ), (26520327962703/100000000000000 : ℝ), (1550319381679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1647772653/2500000000 : ℝ)|^17 ≤ (14494119554023/25000000000000 : ℝ)^13
        have hw : |(1647772653/2500000000 : ℝ)|=(1647772653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3624160201/10000000000 : ℝ)|^17 ≤ (26520327962703/100000000000000 : ℝ)^13
        have hw : |(-3624160201/10000000000 : ℝ)|=(3624160201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2403866313/10000000000 : ℝ)|^17 ≤ (1550319381679/10000000000000 : ℝ)^13
        have hw : |(2403866313/10000000000 : ℝ)|=(2403866313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^17 ≤ (1 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*1^13 ≤ 1^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^17 ≤ (1 : ℝ)^13
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3174712243/10000000000 : ℝ)*x 0 + (-3820578337/10000000000 : ℝ)*x 1 + (-5820867379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3174712243/10000000000 : ℝ)^17 ≤ (892159747541/4000000000000 : ℝ)^13 := by
    have hnat : (3174712243 : ℕ)^17*4000000000000^13 ≤ 892159747541^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174712243 10000000000 892159747541 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3820578337/10000000000 : ℝ)^17 ≤ (28415378809361/100000000000000 : ℝ)^13 := by
    have hnat : (3820578337 : ℕ)^17*100000000000000^13 ≤ 28415378809361^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3820578337 10000000000 28415378809361 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5820867379/10000000000 : ℝ)^17 ≤ (12320156871701/25000000000000 : ℝ)^13 := by
    have hnat : (5820867379 : ℕ)^17*25000000000000^13 ≤ 12320156871701^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5820867379 10000000000 12320156871701 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3174712243/10000000000 : ℝ), (-3820578337/10000000000 : ℝ), (-5820867379/10000000000 : ℝ)] ![(892159747541/4000000000000 : ℝ), (28415378809361/100000000000000 : ℝ), (12320156871701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3174712243/10000000000 : ℝ)|^17 ≤ (892159747541/4000000000000 : ℝ)^13
        have hw : |(-3174712243/10000000000 : ℝ)|=(3174712243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3820578337/10000000000 : ℝ)|^17 ≤ (28415378809361/100000000000000 : ℝ)^13
        have hw : |(-3820578337/10000000000 : ℝ)|=(3820578337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5820867379/10000000000 : ℝ)|^17 ≤ (12320156871701/25000000000000 : ℝ)^13
        have hw : |(-5820867379/10000000000 : ℝ)|=(5820867379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (68420307/200000000 : ℝ)*x 0 + (6008315729/10000000000 : ℝ)*x 1 + (-3362049411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68420307/200000000 : ℝ)^17 ≤ (12296686787869/50000000000000 : ℝ)^13 := by
    have hnat : (68420307 : ℕ)^17*50000000000000^13 ≤ 12296686787869^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68420307 200000000 12296686787869 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6008315729/10000000000 : ℝ)^17 ≤ (51366108891331/100000000000000 : ℝ)^13 := by
    have hnat : (6008315729 : ℕ)^17*100000000000000^13 ≤ 51366108891331^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008315729 10000000000 51366108891331 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3362049411/10000000000 : ℝ)^17 ≤ (24040517515799/100000000000000 : ℝ)^13 := by
    have hnat : (3362049411 : ℕ)^17*100000000000000^13 ≤ 24040517515799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362049411 10000000000 24040517515799 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68420307/200000000 : ℝ), (6008315729/10000000000 : ℝ), (-3362049411/10000000000 : ℝ)] ![(12296686787869/50000000000000 : ℝ), (51366108891331/100000000000000 : ℝ), (24040517515799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68420307/200000000 : ℝ)|^17 ≤ (12296686787869/50000000000000 : ℝ)^13
        have hw : |(68420307/200000000 : ℝ)|=(68420307/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6008315729/10000000000 : ℝ)|^17 ≤ (51366108891331/100000000000000 : ℝ)^13
        have hw : |(6008315729/10000000000 : ℝ)|=(6008315729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3362049411/10000000000 : ℝ)|^17 ≤ (24040517515799/100000000000000 : ℝ)^13
        have hw : |(-3362049411/10000000000 : ℝ)|=(3362049411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (81207307/125000000 : ℝ)*x 0 + (-132204703/400000000 : ℝ)*x 1 + (71895373/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81207307/125000000 : ℝ)^17 ≤ (11378361724147/20000000000000 : ℝ)^13 := by
    have hnat : (81207307 : ℕ)^17*20000000000000^13 ≤ 11378361724147^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81207307 125000000 11378361724147 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132204703/400000000 : ℝ)^17 ≤ (11754777952179/50000000000000 : ℝ)^13 := by
    have hnat : (132204703 : ℕ)^17*50000000000000^13 ≤ 11754777952179^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132204703 400000000 11754777952179 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71895373/250000000 : ℝ)^17 ≤ (19598635454351/100000000000000 : ℝ)^13 := by
    have hnat : (71895373 : ℕ)^17*100000000000000^13 ≤ 19598635454351^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71895373 250000000 19598635454351 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81207307/125000000 : ℝ), (-132204703/400000000 : ℝ), (71895373/250000000 : ℝ)] ![(11378361724147/20000000000000 : ℝ), (11754777952179/50000000000000 : ℝ), (19598635454351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81207307/125000000 : ℝ)|^17 ≤ (11378361724147/20000000000000 : ℝ)^13
        have hw : |(81207307/125000000 : ℝ)|=(81207307/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132204703/400000000 : ℝ)|^17 ≤ (11754777952179/50000000000000 : ℝ)^13
        have hw : |(-132204703/400000000 : ℝ)|=(132204703/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71895373/250000000 : ℝ)|^17 ≤ (19598635454351/100000000000000 : ℝ)^13
        have hw : |(71895373/250000000 : ℝ)|=(71895373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-11071487/39062500 : ℝ)*x 0 + (-3023881637/10000000000 : ℝ)*x 1 + (-1688166191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11071487/39062500 : ℝ)^17 ≤ (4807372224137/25000000000000 : ℝ)^13 := by
    have hnat : (11071487 : ℕ)^17*25000000000000^13 ≤ 4807372224137^13*39062500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11071487 39062500 4807372224137 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3023881637/10000000000 : ℝ)^17 ≤ (2616065307501/12500000000000 : ℝ)^13 := by
    have hnat : (3023881637 : ℕ)^17*12500000000000^13 ≤ 2616065307501^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3023881637 10000000000 2616065307501 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688166191/2500000000 : ℝ)^17 ≤ (59841988633237/100000000000000 : ℝ)^13 := by
    have hnat : (1688166191 : ℕ)^17*100000000000000^13 ≤ 59841988633237^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688166191 2500000000 59841988633237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11071487/39062500 : ℝ), (-3023881637/10000000000 : ℝ), (-1688166191/2500000000 : ℝ)] ![(4807372224137/25000000000000 : ℝ), (2616065307501/12500000000000 : ℝ), (59841988633237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11071487/39062500 : ℝ)|^17 ≤ (4807372224137/25000000000000 : ℝ)^13
        have hw : |(-11071487/39062500 : ℝ)|=(11071487/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3023881637/10000000000 : ℝ)|^17 ≤ (2616065307501/12500000000000 : ℝ)^13
        have hw : |(-3023881637/10000000000 : ℝ)|=(3023881637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688166191/2500000000 : ℝ)|^17 ≤ (59841988633237/100000000000000 : ℝ)^13
        have hw : |(-1688166191/2500000000 : ℝ)|=(1688166191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2203680527/5000000000 : ℝ)*x 0 + (2678154121/5000000000 : ℝ)*x 1 + (-1545909463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203680527/5000000000 : ℝ)^17 ≤ (17126362629741/50000000000000 : ℝ)^13 := by
    have hnat : (2203680527 : ℕ)^17*50000000000000^13 ≤ 17126362629741^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203680527 5000000000 17126362629741 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2678154121/5000000000 : ℝ)^17 ≤ (11050440467839/25000000000000 : ℝ)^13 := by
    have hnat : (2678154121 : ℕ)^17*25000000000000^13 ≤ 11050440467839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678154121 5000000000 11050440467839 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545909463/5000000000 : ℝ)^17 ≤ (21545512860987/100000000000000 : ℝ)^13 := by
    have hnat : (1545909463 : ℕ)^17*100000000000000^13 ≤ 21545512860987^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545909463 5000000000 21545512860987 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2203680527/5000000000 : ℝ), (2678154121/5000000000 : ℝ), (-1545909463/5000000000 : ℝ)] ![(17126362629741/50000000000000 : ℝ), (11050440467839/25000000000000 : ℝ), (21545512860987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2203680527/5000000000 : ℝ)|^17 ≤ (17126362629741/50000000000000 : ℝ)^13
        have hw : |(2203680527/5000000000 : ℝ)|=(2203680527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2678154121/5000000000 : ℝ)|^17 ≤ (11050440467839/25000000000000 : ℝ)^13
        have hw : |(2678154121/5000000000 : ℝ)|=(2678154121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1545909463/5000000000 : ℝ)|^17 ≤ (21545512860987/100000000000000 : ℝ)^13
        have hw : |(-1545909463/5000000000 : ℝ)|=(1545909463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7445888803/10000000000 : ℝ)*x 0 + (-1544170023/5000000000 : ℝ)*x 1 + (55708777/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7445888803/10000000000 : ℝ)^17 ≤ (3399979175323/5000000000000 : ℝ)^13 := by
    have hnat : (7445888803 : ℕ)^17*5000000000000^13 ≤ 3399979175323^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7445888803 10000000000 3399979175323 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544170023/5000000000 : ℝ)^17 ≤ (4302763253389/20000000000000 : ℝ)^13 := by
    have hnat : (1544170023 : ℕ)^17*20000000000000^13 ≤ 4302763253389^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544170023 5000000000 4302763253389 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55708777/312500000 : ℝ)^17 ≤ (2621650051261/25000000000000 : ℝ)^13 := by
    have hnat : (55708777 : ℕ)^17*25000000000000^13 ≤ 2621650051261^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55708777 312500000 2621650051261 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7445888803/10000000000 : ℝ), (-1544170023/5000000000 : ℝ), (55708777/312500000 : ℝ)] ![(3399979175323/5000000000000 : ℝ), (4302763253389/20000000000000 : ℝ), (2621650051261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7445888803/10000000000 : ℝ)|^17 ≤ (3399979175323/5000000000000 : ℝ)^13
        have hw : |(7445888803/10000000000 : ℝ)|=(7445888803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1544170023/5000000000 : ℝ)|^17 ≤ (4302763253389/20000000000000 : ℝ)^13
        have hw : |(-1544170023/5000000000 : ℝ)|=(1544170023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55708777/312500000 : ℝ)|^17 ≤ (2621650051261/25000000000000 : ℝ)^13
        have hw : |(55708777/312500000 : ℝ)|=(55708777/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828924001/5000000000 : ℝ)*x 0 + (-35797041/80000000 : ℝ)*x 1 + (-599066973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828924001/5000000000 : ℝ)^17 ≤ (6710788588373/25000000000000 : ℝ)^13 := by
    have hnat : (1828924001 : ℕ)^17*25000000000000^13 ≤ 6710788588373^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828924001 5000000000 6710788588373 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35797041/80000000 : ℝ)^17 ≤ (34937980755669/100000000000000 : ℝ)^13 := by
    have hnat : (35797041 : ℕ)^17*100000000000000^13 ≤ 34937980755669^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35797041 80000000 34937980755669 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599066973/1250000000 : ℝ)^17 ≤ (9554716217913/25000000000000 : ℝ)^13 := by
    have hnat : (599066973 : ℕ)^17*25000000000000^13 ≤ 9554716217913^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599066973 1250000000 9554716217913 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828924001/5000000000 : ℝ), (-35797041/80000000 : ℝ), (-599066973/1250000000 : ℝ)] ![(6710788588373/25000000000000 : ℝ), (34937980755669/100000000000000 : ℝ), (9554716217913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828924001/5000000000 : ℝ)|^17 ≤ (6710788588373/25000000000000 : ℝ)^13
        have hw : |(-1828924001/5000000000 : ℝ)|=(1828924001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35797041/80000000 : ℝ)|^17 ≤ (34937980755669/100000000000000 : ℝ)^13
        have hw : |(-35797041/80000000 : ℝ)|=(35797041/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-599066973/1250000000 : ℝ)|^17 ≤ (9554716217913/25000000000000 : ℝ)^13
        have hw : |(-599066973/1250000000 : ℝ)|=(599066973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (73685537/250000000 : ℝ)*x 0 + (1512618817/2500000000 : ℝ)*x 1 + (-188491597/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73685537/250000000 : ℝ)^17 ≤ (10119608433511/50000000000000 : ℝ)^13 := by
    have hnat : (73685537 : ℕ)^17*50000000000000^13 ≤ 10119608433511^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73685537 250000000 10119608433511 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512618817/2500000000 : ℝ)^17 ≤ (51837947162493/100000000000000 : ℝ)^13 := by
    have hnat : (1512618817 : ℕ)^17*100000000000000^13 ≤ 51837947162493^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512618817 2500000000 51837947162493 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188491597/500000000 : ℝ)^17 ≤ (13961417980631/50000000000000 : ℝ)^13 := by
    have hnat : (188491597 : ℕ)^17*50000000000000^13 ≤ 13961417980631^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188491597 500000000 13961417980631 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(73685537/250000000 : ℝ), (1512618817/2500000000 : ℝ), (-188491597/500000000 : ℝ)] ![(10119608433511/50000000000000 : ℝ), (51837947162493/100000000000000 : ℝ), (13961417980631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(73685537/250000000 : ℝ)|^17 ≤ (10119608433511/50000000000000 : ℝ)^13
        have hw : |(73685537/250000000 : ℝ)|=(73685537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1512618817/2500000000 : ℝ)|^17 ≤ (51837947162493/100000000000000 : ℝ)^13
        have hw : |(1512618817/2500000000 : ℝ)|=(1512618817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188491597/500000000 : ℝ)|^17 ≤ (13961417980631/50000000000000 : ℝ)^13
        have hw : |(-188491597/500000000 : ℝ)|=(188491597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s0_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (75217139/100000000 : ℝ)*x 0 + (-2943965689/10000000000 : ℝ)*x 1 + (366855673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75217139/100000000 : ℝ)^17 ≤ (6890654016357/10000000000000 : ℝ)^13 := by
    have hnat : (75217139 : ℕ)^17*10000000000000^13 ≤ 6890654016357^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75217139 100000000 6890654016357 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2943965689/10000000000 : ℝ)^17 ≤ (20208190842519/100000000000000 : ℝ)^13 := by
    have hnat : (2943965689 : ℕ)^17*100000000000000^13 ≤ 20208190842519^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2943965689 10000000000 20208190842519 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366855673/2000000000 : ℝ)^17 ≤ (5442634485777/50000000000000 : ℝ)^13 := by
    have hnat : (366855673 : ℕ)^17*50000000000000^13 ≤ 5442634485777^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366855673 2000000000 5442634485777 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(75217139/100000000 : ℝ), (-2943965689/10000000000 : ℝ), (366855673/2000000000 : ℝ)] ![(6890654016357/10000000000000 : ℝ), (20208190842519/100000000000000 : ℝ), (5442634485777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(75217139/100000000 : ℝ)|^17 ≤ (6890654016357/10000000000000 : ℝ)^13
        have hw : |(75217139/100000000 : ℝ)|=(75217139/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2943965689/10000000000 : ℝ)|^17 ≤ (20208190842519/100000000000000 : ℝ)^13
        have hw : |(-2943965689/10000000000 : ℝ)|=(2943965689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(366855673/2000000000 : ℝ)|^17 ≤ (5442634485777/50000000000000 : ℝ)^13
        have hw : |(366855673/2000000000 : ℝ)|=(366855673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-370494817/1000000000 : ℝ)*x 0 + (-1852474053/5000000000 : ℝ)*x 1 + (-2733861237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370494817/1000000000 : ℝ)^17 ≤ (13648022246799/50000000000000 : ℝ)^13 := by
    have hnat : (370494817 : ℕ)^17*50000000000000^13 ≤ 13648022246799^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370494817 1000000000 13648022246799 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852474053/5000000000 : ℝ)^17 ≤ (27296043876999/100000000000000 : ℝ)^13 := by
    have hnat : (1852474053 : ℕ)^17*100000000000000^13 ≤ 27296043876999^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852474053 5000000000 27296043876999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733861237/5000000000 : ℝ)^17 ≤ (45407911612591/100000000000000 : ℝ)^13 := by
    have hnat : (2733861237 : ℕ)^17*100000000000000^13 ≤ 45407911612591^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733861237 5000000000 45407911612591 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370494817/1000000000 : ℝ), (-1852474053/5000000000 : ℝ), (-2733861237/5000000000 : ℝ)] ![(13648022246799/50000000000000 : ℝ), (27296043876999/100000000000000 : ℝ), (45407911612591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370494817/1000000000 : ℝ)|^17 ≤ (13648022246799/50000000000000 : ℝ)^13
        have hw : |(-370494817/1000000000 : ℝ)|=(370494817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852474053/5000000000 : ℝ)|^17 ≤ (27296043876999/100000000000000 : ℝ)^13
        have hw : |(-1852474053/5000000000 : ℝ)|=(1852474053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2733861237/5000000000 : ℝ)|^17 ≤ (45407911612591/100000000000000 : ℝ)^13
        have hw : |(-2733861237/5000000000 : ℝ)|=(2733861237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2368957237/5000000000 : ℝ)*x 0 + (4737914393/10000000000 : ℝ)*x 1 + (-1716149031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2368957237/5000000000 : ℝ)^17 ≤ (37650253003647/100000000000000 : ℝ)^13 := by
    have hnat : (2368957237 : ℕ)^17*100000000000000^13 ≤ 37650253003647^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368957237 5000000000 37650253003647 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4737914393/10000000000 : ℝ)^17 ≤ (58828519003/156250000000 : ℝ)^13 := by
    have hnat : (4737914393 : ℕ)^17*156250000000^13 ≤ 58828519003^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737914393 10000000000 58828519003 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1716149031/5000000000 : ℝ)^17 ≤ (493989896191/2000000000000 : ℝ)^13 := by
    have hnat : (1716149031 : ℕ)^17*2000000000000^13 ≤ 493989896191^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716149031 5000000000 493989896191 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2368957237/5000000000 : ℝ), (4737914393/10000000000 : ℝ), (-1716149031/5000000000 : ℝ)] ![(37650253003647/100000000000000 : ℝ), (58828519003/156250000000 : ℝ), (493989896191/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2368957237/5000000000 : ℝ)|^17 ≤ (37650253003647/100000000000000 : ℝ)^13
        have hw : |(2368957237/5000000000 : ℝ)|=(2368957237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4737914393/10000000000 : ℝ)|^17 ≤ (58828519003/156250000000 : ℝ)^13
        have hw : |(4737914393/10000000000 : ℝ)|=(4737914393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1716149031/5000000000 : ℝ)|^17 ≤ (493989896191/2000000000000 : ℝ)^13
        have hw : |(-1716149031/5000000000 : ℝ)|=(1716149031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2368957237/5000000000 : ℝ)*x 0 + (-4737914393/10000000000 : ℝ)*x 1 + (1716149031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2368957237/5000000000 : ℝ)^17 ≤ (37650253003647/100000000000000 : ℝ)^13 := by
    have hnat : (2368957237 : ℕ)^17*100000000000000^13 ≤ 37650253003647^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368957237 5000000000 37650253003647 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4737914393/10000000000 : ℝ)^17 ≤ (58828519003/156250000000 : ℝ)^13 := by
    have hnat : (4737914393 : ℕ)^17*156250000000^13 ≤ 58828519003^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737914393 10000000000 58828519003 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1716149031/5000000000 : ℝ)^17 ≤ (493989896191/2000000000000 : ℝ)^13 := by
    have hnat : (1716149031 : ℕ)^17*2000000000000^13 ≤ 493989896191^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716149031 5000000000 493989896191 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2368957237/5000000000 : ℝ), (-4737914393/10000000000 : ℝ), (1716149031/5000000000 : ℝ)] ![(37650253003647/100000000000000 : ℝ), (58828519003/156250000000 : ℝ), (493989896191/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2368957237/5000000000 : ℝ)|^17 ≤ (37650253003647/100000000000000 : ℝ)^13
        have hw : |(2368957237/5000000000 : ℝ)|=(2368957237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4737914393/10000000000 : ℝ)|^17 ≤ (58828519003/156250000000 : ℝ)^13
        have hw : |(-4737914393/10000000000 : ℝ)|=(4737914393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1716149031/5000000000 : ℝ)|^17 ≤ (493989896191/2000000000000 : ℝ)^13
        have hw : |(1716149031/5000000000 : ℝ)|=(1716149031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307064_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (370494817/1000000000 : ℝ)*x 0 + (-1852474053/5000000000 : ℝ)*x 1 + (-2733861237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370494817/1000000000 : ℝ)^17 ≤ (13648022246799/50000000000000 : ℝ)^13 := by
    have hnat : (370494817 : ℕ)^17*50000000000000^13 ≤ 13648022246799^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370494817 1000000000 13648022246799 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852474053/5000000000 : ℝ)^17 ≤ (27296043876999/100000000000000 : ℝ)^13 := by
    have hnat : (1852474053 : ℕ)^17*100000000000000^13 ≤ 27296043876999^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852474053 5000000000 27296043876999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733861237/5000000000 : ℝ)^17 ≤ (45407911612591/100000000000000 : ℝ)^13 := by
    have hnat : (2733861237 : ℕ)^17*100000000000000^13 ≤ 45407911612591^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733861237 5000000000 45407911612591 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(370494817/1000000000 : ℝ), (-1852474053/5000000000 : ℝ), (-2733861237/5000000000 : ℝ)] ![(13648022246799/50000000000000 : ℝ), (27296043876999/100000000000000 : ℝ), (45407911612591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(370494817/1000000000 : ℝ)|^17 ≤ (13648022246799/50000000000000 : ℝ)^13
        have hw : |(370494817/1000000000 : ℝ)|=(370494817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852474053/5000000000 : ℝ)|^17 ≤ (27296043876999/100000000000000 : ℝ)^13
        have hw : |(-1852474053/5000000000 : ℝ)|=(1852474053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2733861237/5000000000 : ℝ)|^17 ≤ (45407911612591/100000000000000 : ℝ)^13
        have hw : |(-2733861237/5000000000 : ℝ)|=(2733861237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307064 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-404327261/1250000000 : ℝ)*X 0 0+(-3762221747/10000000000 : ℝ)*X 0 1+(-5822156573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3471811209/10000000000 : ℝ)*X 1 0+(5639811963/10000000000 : ℝ)*X 1 1+(-1870413177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1647772653/2500000000 : ℝ)*X 2 0+(-3624160201/10000000000 : ℝ)*X 2 1+(2403866313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3174712243/10000000000 : ℝ)*X 0 0+(-3820578337/10000000000 : ℝ)*X 0 1+(-5820867379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((68420307/200000000 : ℝ)*X 1 0+(6008315729/10000000000 : ℝ)*X 1 1+(-3362049411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((81207307/125000000 : ℝ)*X 2 0+(-132204703/400000000 : ℝ)*X 2 1+(71895373/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-11071487/39062500 : ℝ)*X 0 0+(-3023881637/10000000000 : ℝ)*X 0 1+(-1688166191/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2203680527/5000000000 : ℝ)*X 1 0+(2678154121/5000000000 : ℝ)*X 1 1+(-1545909463/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7445888803/10000000000 : ℝ)*X 2 0+(-1544170023/5000000000 : ℝ)*X 2 1+(55708777/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1828924001/5000000000 : ℝ)*X 0 0+(-35797041/80000000 : ℝ)*X 0 1+(-599066973/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((73685537/250000000 : ℝ)*X 1 0+(1512618817/2500000000 : ℝ)*X 1 1+(-188491597/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((75217139/100000000 : ℝ)*X 2 0+(-2943965689/10000000000 : ℝ)*X 2 1+(366855673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31254256963865173762023/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1832976088051/1000000000000 : ℝ)*(base1) + (167238007849/1000000000000 : ℝ)*(base7) + (6889611/1000000000000 : ℝ)*(base22) + (11351067673/10000000000 : ℝ)*(base39) + (111772772621/125000000000 : ℝ)*(base60) + (2589356530913/1000000000000 : ℝ)*(major_s0_0) + (2589356530913/1000000000000 : ℝ)*(major_s0_1) + (2589356530913/1000000000000 : ℝ)*(major_s0_2) + (428089/250000000000 : ℝ)*(sp_s0_1) + (2621376518439/500000000000 : ℝ)*(sp_s0_7) + (3409645779083/1000000000000 : ℝ)*(sp_s0_8) + (3409770123267/1000000000000 : ℝ)*(sp_s0_9) + (64051/1000000000000 : ℝ)*(sp_s0_14) + (129521439/1000000000000 : ℝ)*(sp_s0_21) + (832869040101/500000000000 : ℝ)*(f.failure) + (1704888506439/500000000000 : ℝ)*(f.sum) + (4354964218412659/10000000000000000000000000000 : ℝ)*base62 + (878636847932359/2000000000000000000000000000 : ℝ)*base65 + (199528507462773/5000000000000000000000000000 : ℝ)*base67 + (2350788442537227/5000000000000000000000000000 : ℝ)*base68 + (3520403590736249/10000000000000000000000000000 : ℝ)*base71 + (808784186067641/2000000000000000000000000000 : ℝ)*base73 + (197483330667641/2000000000000000000000000000 : ℝ)*base74 + (272031118037227/5000000000000000000000000000 : ℝ)*base77 + (2954770782263751/10000000000000000000000000000 : ℝ)*base79 + (3719/6250000000000000 : ℝ)*base86 + (3719/6250000000000000 : ℝ)*base88 + (3719/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-37141/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-37141/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6277216483884086850831/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3778431911839/1000000000000 : ℝ)*(base1) + (574250945507/500000000000 : ℝ)*(base7) + (679905281511/500000000000 : ℝ)*(base39) + (1225991717009/1000000000000 : ℝ)*(base60) + (2073479111161/200000000000 : ℝ)*(major_s0_0) + (4088173618773/1000000000000 : ℝ)*(major_s0_1) + (4088173618773/1000000000000 : ℝ)*(major_s0_2) + (16161711/1000000000000 : ℝ)*(sp_s0_0) + (3169193/100000000000 : ℝ)*(sp_s0_2) + (784902742129/125000000000 : ℝ)*(sp_s0_3) + (861613629757/100000000000 : ℝ)*(sp_s0_14) + (2418860273721/500000000000 : ℝ)*(sp_s0_15) + (604684889897/125000000000 : ℝ)*(sp_s0_16) + (13108521/62500000000 : ℝ)*(sp_s0_22) + (1314965010413/500000000000 : ℝ)*(f.failure) + (2418860273721/500000000000 : ℝ)*(f.sum) + (1911372936138639/10000000000000000000000000000 : ℝ)*base62 + (295798162907661/2000000000000000000000000000 : ℝ)*base64 + (1718963319800167/5000000000000000000000000000 : ℝ)*base66 + (422274804699833/5000000000000000000000000000 : ℝ)*base69 + (520104043945177/2000000000000000000000000000 : ℝ)*base71 + (90045025479377/400000000000000000000000000 : ℝ)*base73 + (366188018092339/2000000000000000000000000000 : ℝ)*base75 + (46655473526419/1000000000000000000000000000 : ℝ)*base77 + (3238539028384091/10000000000000000000000000000 : ℝ)*base79 + (3753/6250000000000000 : ℝ)*base87 + (3753/6250000000000000 : ℝ)*base89 + (3753/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-27163/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-27163/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10165492844896989383163/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62149456147/20000000000 : ℝ)*(base1) + (988862316667/1000000000000 : ℝ)*(base7) + (42270224261/500000000000 : ℝ)*(base40) + (56816549263/100000000000 : ℝ)*(base60) + (11609188013027/1000000000000 : ℝ)*(major_s0_0) + (3293337635557/1000000000000 : ℝ)*(major_s0_1) + (3293337635557/1000000000000 : ℝ)*(major_s0_2) + (831585037747/100000000000 : ℝ)*(sp_s0_3) + (20095443/1000000000000 : ℝ)*(sp_s0_7) + (102928521/1000000000000 : ℝ)*(sp_s0_8) + (62505007/200000000000 : ℝ)*(sp_s0_16) + (3482661667107/500000000000 : ℝ)*(sp_s0_20) + (3857767693787/1000000000000 : ℝ)*(sp_s0_21) + (3857558097273/1000000000000 : ℝ)*(sp_s0_22) + (2118610490683/1000000000000 : ℝ)*(f.failure) + (964467655577/250000000000 : ℝ)*(f.sum) + (1718528775991551/10000000000000000000000000000 : ℝ)*base62 + (1703236431285149/2000000000000000000000000000 : ℝ)*base64 + (3881756491282903/5000000000000000000000000000 : ℝ)*base66 + (2332288617217097/5000000000000000000000000000 : ℝ)*base69 + (2528033459481679/10000000000000000000000000000 : ℝ)*base70 + (830435784935061/2000000000000000000000000000 : ℝ)*base72 + (647624999514851/2000000000000000000000000000 : ℝ)*base75 + (2136875915027967/5000000000000000000000000000 : ℝ)*base76 + (947596376241111/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1127/12500000000000000 : ℝ)*base86 + (1127/12500000000000000 : ℝ)*base88 + (1127/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (6631/100000 : ℝ) ^ (135/32 : ℝ) ≤ (53395729999091/5000000000000000000 : ℝ) := by
    have hpowers : (6631/100000 : ℝ)^135 ≤ (53395729999091/5000000000000000000 : ℝ)^32 := by
      have hnat : (6631 : ℕ)^135*5000000000000000000^32 ≤ 53395729999091^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6631 100000 53395729999091 5000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6631/100000 : ℝ)) (X := (53395729999091/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5000053395729999091/5000000000000000000 : ℝ) ≤ (2000005062685627/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (5000053395729999091/5000000000000000000 : ℝ)^32 ≤ (2000005062685627/2000000000000000 : ℝ)^135 := by
      have hnat : (5000053395729999091 : ℕ)^32*2000000000000000^135 ≤ 2000005062685627^135*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000053395729999091 5000000000000000000 2000005062685627 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005062685627/2000000000000000 : ℝ)) (X := (5000053395729999091/5000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2500053395729999091/2500000000000000000 : ℝ) ≤ (400002025066001/400000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2500053395729999091/2500000000000000000 : ℝ)^32 ≤ (400002025066001/400000000000000 : ℝ)^135 := by
      have hnat : (2500053395729999091 : ℕ)^32*400000000000000^135 ≤ 400002025066001^135*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500053395729999091 2500000000000000000 400002025066001 400000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002025066001/400000000000000 : ℝ)) (X := (2500053395729999091/2500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5062685627/132620000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2531322189/66310000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (6631/100000 : ℝ)) (alpha := (5062685627/132620000000000 : ℝ)) (beta := (2531322189/66310000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6631/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5062685627/132620000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2531322189/66310000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (37141/50000 : ℝ) ^ (135/32 : ℝ) ≤ (1783077236710002461/6250000000000000000 : ℝ) := by
    have hpowers : (37141/50000 : ℝ)^135 ≤ (1783077236710002461/6250000000000000000 : ℝ)^32 := by
      have hnat : (37141 : ℕ)^135*6250000000000000000^32 ≤ 1783077236710002461^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37141 50000 1783077236710002461 6250000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37141/50000 : ℝ)) (X := (1783077236710002461/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (8033077236710002461/6250000000000000000 : ℝ) ≤ (2653245901720827/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (8033077236710002461/6250000000000000000 : ℝ)^32 ≤ (2653245901720827/2500000000000000 : ℝ)^135 := by
      have hnat : (8033077236710002461 : ℕ)^32*2500000000000000^135 ≤ 2653245901720827^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8033077236710002461 6250000000000000000 2653245901720827 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2653245901720827/2500000000000000 : ℝ)) (X := (8033077236710002461/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (4908077236710002461/3125000000000000000 : ℝ) ≤ (11129452633001847/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (4908077236710002461/3125000000000000000 : ℝ)^32 ≤ (11129452633001847/10000000000000000 : ℝ)^135 := by
      have hnat : (4908077236710002461 : ℕ)^32*10000000000000000^135 ≤ 11129452633001847^135*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4908077236710002461 3125000000000000000 11129452633001847 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11129452633001847/10000000000000000 : ℝ)) (X := (4908077236710002461/3125000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(153245901720827/1857050000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(39728386624503/571400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (37141/50000 : ℝ)) (alpha := (153245901720827/1857050000000000 : ℝ)) (beta := (39728386624503/571400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (37141/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(153245901720827/1857050000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(39728386624503/571400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (27163/50000 : ℝ) ^ (135/32 : ℝ) ≤ (7621910731386376051/100000000000000000000 : ℝ) := by
    have hpowers : (27163/50000 : ℝ)^135 ≤ (7621910731386376051/100000000000000000000 : ℝ)^32 := by
      have hnat : (27163 : ℕ)^135*100000000000000000000^32 ≤ 7621910731386376051^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27163 50000 7621910731386376051 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27163/50000 : ℝ)) (X := (7621910731386376051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (107621910731386376051/100000000000000000000 : ℝ) ≤ (10175637965348903/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (107621910731386376051/100000000000000000000 : ℝ)^32 ≤ (10175637965348903/10000000000000000 : ℝ)^135 := by
      have hnat : (107621910731386376051 : ℕ)^32*10000000000000000^135 ≤ 10175637965348903^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107621910731386376051 100000000000000000000 10175637965348903 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10175637965348903/10000000000000000 : ℝ)) (X := (107621910731386376051/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (57621910731386376051/50000000000000000000 : ℝ) ≤ (10342026956220199/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (57621910731386376051/50000000000000000000 : ℝ)^32 ≤ (10342026956220199/10000000000000000 : ℝ)^135 := by
      have hnat : (57621910731386376051 : ℕ)^32*10000000000000000^135 ≤ 10342026956220199^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57621910731386376051 50000000000000000000 10342026956220199 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10342026956220199/10000000000000000 : ℝ)) (X := (57621910731386376051/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(175637965348903/5432600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(649956995591/21221093750000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (27163/50000 : ℝ)) (alpha := (175637965348903/5432600000000000 : ℝ)) (beta := (649956995591/21221093750000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (27163/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(175637965348903/5432600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(649956995591/21221093750000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-370494817/1000000000 : ℝ)*X 0 0+(-1852474053/5000000000 : ℝ)*X 0 1+(-2733861237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2368957237/5000000000 : ℝ)*X 1 0+(4737914393/10000000000 : ℝ)*X 1 1+(-1716149031/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2368957237/5000000000 : ℝ)*X 2 0+(-4737914393/10000000000 : ℝ)*X 2 1+(1716149031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((370494817/1000000000 : ℝ)*X 0 0+(-1852474053/5000000000 : ℝ)*X 0 1+(-2733861237/5000000000 : ℝ)*X 0 2+(370494817/1000000000 : ℝ)*X 1 0+(-1852474053/5000000000 : ℝ)*X 1 1+(-2733861237/5000000000 : ℝ)*X 1 2+(370494817/1000000000 : ℝ)*X 2 0+(-1852474053/5000000000 : ℝ)*X 2 1+(-2733861237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307064_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-39543/6250 : ℝ) < ((-19431/12500 : ℝ)*P 0+(-19431/12500 : ℝ)*P 1+(-19431/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-39543/6250 : ℝ) < (-1688110502679074459260055302779351/270840371590000000000000000000000 : ℝ) := by norm_num
    linear_combination (210852180763/250000000000 : ℝ)*(base1) + (45029/1000000000000 : ℝ)*(base12) + (48187/1000000000000 : ℝ)*(base22) + (1267745212191/1000000000000 : ℝ)*(base39) + (25602279307/50000000000 : ℝ)*(base40) + (40402483969/100000000000 : ℝ)*(base49) + (92369604927/200000000000 : ℝ)*(base60) + (19431/12500 : ℝ)*(major_s1_0) + (19431/12500 : ℝ)*(major_s1_1) + (19431/12500 : ℝ)*(major_s1_2) + (2921029140547/1000000000000 : ℝ)*(sp_s1_0) + (519405115631/250000000000 : ℝ)*(sp_s1_1) + (415524083901/200000000000 : ℝ)*(sp_s1_2) + (39147819237/250000000000 : ℝ)*(sp_s1_6) + (519405115631/250000000000 : ℝ)*(f.sum) + (43329944193397347/77604691000000000000000000000 : ℝ)*base62 + (1619639754861/27163000000000000000000000 : ℝ)*base65 + (180053916083/37141000000000000000000000 : ℝ)*base67 + (216452767199/8488437500000000000000000 : ℝ)*base68 + (117242978501695567/450294632500000000000000000000 : ℝ)*base71 + (424102437037/828875000000000000000000 : ℝ)*base72 + (14764916072391421/2857000000000000000000000 : ℝ)*base74 + (28188949664343/66310000000000000000000000 : ℝ)*base77 + (621829346952913609/1231409855000000000000000000000 : ℝ)*base78 + (323/62500000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c307065_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154732869/5000000000 : ℝ)*x 0 + (-2460668269/5000000000 : ℝ)*x 1 + (1845991291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154732869/5000000000 : ℝ)^17 ≤ (8315308056909/25000000000000 : ℝ)^13 := by
    have hnat : (2154732869 : ℕ)^17*25000000000000^13 ≤ 8315308056909^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154732869 5000000000 8315308056909 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2460668269/5000000000 : ℝ)^17 ≤ (2472973198027/6250000000000 : ℝ)^13 := by
    have hnat : (2460668269 : ℕ)^17*6250000000000^13 ≤ 2472973198027^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460668269 5000000000 2472973198027 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845991291/5000000000 : ℝ)^17 ≤ (6792799144573/25000000000000 : ℝ)^13 := by
    have hnat : (1845991291 : ℕ)^17*25000000000000^13 ≤ 6792799144573^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845991291 5000000000 6792799144573 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154732869/5000000000 : ℝ), (-2460668269/5000000000 : ℝ), (1845991291/5000000000 : ℝ)] ![(8315308056909/25000000000000 : ℝ), (2472973198027/6250000000000 : ℝ), (6792799144573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154732869/5000000000 : ℝ)|^17 ≤ (8315308056909/25000000000000 : ℝ)^13
        have hw : |(-2154732869/5000000000 : ℝ)|=(2154732869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2460668269/5000000000 : ℝ)|^17 ≤ (2472973198027/6250000000000 : ℝ)^13
        have hw : |(-2460668269/5000000000 : ℝ)|=(2460668269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1845991291/5000000000 : ℝ)|^17 ≤ (6792799144573/25000000000000 : ℝ)^13
        have hw : |(1845991291/5000000000 : ℝ)|=(1845991291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307065_s0_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3681643459/10000000000 : ℝ)*x 0 + (4231585769/10000000000 : ℝ)*x 1 + (5005131707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3681643459/10000000000 : ℝ)^17 ≤ (27071735967593/100000000000000 : ℝ)^13 := by
    have hnat : (3681643459 : ℕ)^17*100000000000000^13 ≤ 27071735967593^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681643459 10000000000 27071735967593 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231585769/10000000000 : ℝ)^17 ≤ (32477383948129/100000000000000 : ℝ)^13 := by
    have hnat : (4231585769 : ℕ)^17*100000000000000^13 ≤ 32477383948129^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231585769 10000000000 32477383948129 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005131707/10000000000 : ℝ)^17 ≤ (40450880073963/100000000000000 : ℝ)^13 := by
    have hnat : (5005131707 : ℕ)^17*100000000000000^13 ≤ 40450880073963^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005131707 10000000000 40450880073963 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3681643459/10000000000 : ℝ), (4231585769/10000000000 : ℝ), (5005131707/10000000000 : ℝ)] ![(27071735967593/100000000000000 : ℝ), (32477383948129/100000000000000 : ℝ), (40450880073963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3681643459/10000000000 : ℝ)|^17 ≤ (27071735967593/100000000000000 : ℝ)^13
        have hw : |(3681643459/10000000000 : ℝ)|=(3681643459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231585769/10000000000 : ℝ)|^17 ≤ (32477383948129/100000000000000 : ℝ)^13
        have hw : |(4231585769/10000000000 : ℝ)|=(4231585769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005131707/10000000000 : ℝ)|^17 ≤ (40450880073963/100000000000000 : ℝ)^13
        have hw : |(5005131707/10000000000 : ℝ)|=(5005131707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307065_s0_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5026502303/10000000000 : ℝ)*x 0 + (-715905707/2000000000 : ℝ)*x 1 + (-67285599/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5026502303/10000000000 : ℝ)^17 ≤ (40676885868673/100000000000000 : ℝ)^13 := by
    have hnat : (5026502303 : ℕ)^17*100000000000000^13 ≤ 40676885868673^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026502303 10000000000 40676885868673 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715905707/2000000000 : ℝ)^17 ≤ (26094048694027/100000000000000 : ℝ)^13 := by
    have hnat : (715905707 : ℕ)^17*100000000000000^13 ≤ 26094048694027^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715905707 2000000000 26094048694027 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67285599/156250000 : ℝ)^17 ≤ (4153633178231/12500000000000 : ℝ)^13 := by
    have hnat : (67285599 : ℕ)^17*12500000000000^13 ≤ 4153633178231^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67285599 156250000 4153633178231 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5026502303/10000000000 : ℝ), (-715905707/2000000000 : ℝ), (-67285599/156250000 : ℝ)] ![(40676885868673/100000000000000 : ℝ), (26094048694027/100000000000000 : ℝ), (4153633178231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5026502303/10000000000 : ℝ)|^17 ≤ (40676885868673/100000000000000 : ℝ)^13
        have hw : |(5026502303/10000000000 : ℝ)|=(5026502303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715905707/2000000000 : ℝ)|^17 ≤ (26094048694027/100000000000000 : ℝ)^13
        have hw : |(-715905707/2000000000 : ℝ)|=(715905707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67285599/156250000 : ℝ)|^17 ≤ (4153633178231/12500000000000 : ℝ)^13
        have hw : |(-67285599/156250000 : ℝ)|=(67285599/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307065 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(892848319012779/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(237789221871257/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (135/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^135 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^135*1^32 ≤ 1^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5892848319012779/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5892848319012779/5000000000000000 : ℝ)^135 := by
      have hnat : (2 : ℕ)^32*5000000000000000^135 ≤ 5892848319012779^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5892848319012779 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5892848319012779/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12974642747381843/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (12974642747381843/10000000000000000 : ℝ)^135 := by
      have hnat : (3 : ℕ)^32*10000000000000000^135 ≤ 12974642747381843^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12974642747381843 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12974642747381843/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (892848319012779/5000000000000000 : ℝ)) (beta := (237789221871257/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(892848319012779/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(237789221871257/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2154732869/5000000000 : ℝ)*X 0 0+(-2460668269/5000000000 : ℝ)*X 0 1+(1845991291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307065_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3681643459/10000000000 : ℝ)*X 1 0+(4231585769/10000000000 : ℝ)*X 1 1+(5005131707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307065_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5026502303/10000000000 : ℝ)*X 2 0+(-715905707/2000000000 : ℝ)*X 2 1+(-67285599/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307065_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-39543/6250 : ℝ) < ((-19431/12500 : ℝ)*P 0+(-19431/12500 : ℝ)*P 1+(-19431/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-39543/6250 : ℝ) < (-7774870465720358121205211613/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (666677850201/1000000000000 : ℝ)*(base1) + (66664409967/200000000000 : ℝ)*(base3) + (86367/500000000000 : ℝ)*(base33) + (24991/250000000000 : ℝ)*(base34) + (534753921193/1000000000000 : ℝ)*(base40) + (592818867147/1000000000000 : ℝ)*(base49) + (66325615633/250000000000 : ℝ)*(base50) + (203953/1000000000000 : ℝ)*(base59) + (195432416133/500000000000 : ℝ)*(base60) + (777239863651/500000000000 : ℝ)*(major_s0_0) + (19431/12500 : ℝ)*(major_s0_1) + (19431/12500 : ℝ)*(major_s0_2) + (2739976541093/1000000000000 : ℝ)*(sp_s0_0) + (1203310333979/500000000000 : ℝ)*(sp_s0_1) + (1036649309061/500000000000 : ℝ)*(sp_s0_2) + (259162348857/125000000000 : ℝ)*(f.sum) + (1952632497/5000000000000000000000 : ℝ)*base63 + (840724617/5000000000000000000000 : ℝ)*base65 + (966320983/5000000000000000000000 : ℝ)*base66 + (124506719/5000000000000000000000 : ℝ)*base69 + (609348238903871/2500000000000000000000000000 : ℝ)*base70 + (82703325379307/1000000000000000000000000000 : ℝ)*base73 + (445779117/5000000000000000000000 : ℝ)*base75 + (1041321295903871/2500000000000000000000000000 : ℝ)*base76 + (153201728820693/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p007_b029 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=62 ∨ c=63 ∨ c=64 ∨ c=65 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c307062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c307064 p hpa (by linarith only [hpb]) X hX
  · exact collision_c307065 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
