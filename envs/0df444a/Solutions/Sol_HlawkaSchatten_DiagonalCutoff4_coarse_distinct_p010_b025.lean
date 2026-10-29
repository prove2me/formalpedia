-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:16:26.164441+00:00
-- url     : https://prove2.me/submissions/09c6e899-0d19-43a8-b78f-46adc9055cb9

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310045 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c310045_s0 p hpa hpb X hX
  have h1 := collision_c310045_s1 p hpa hpb X hX h0
  have h2 := collision_c310045_s2 p hpa hpb X hX h1
  exact collision_c310045_s3 p hpa hpb X hX h2

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
theorem collision_support_c310044_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-818198599/10000000000 : ℝ)*x 0 + (-3347511341/5000000000 : ℝ)*x 1 + (-2273362043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818198599/10000000000 : ℝ)^9 ≤ (7815863743/195312500000 : ℝ)^7 := by
    have hnat : (818198599 : ℕ)^9*195312500000^7 ≤ 7815863743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818198599 10000000000 7815863743 195312500000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3347511341/5000000000 : ℝ)^9 ≤ (11939796382997/20000000000000 : ℝ)^7 := by
    have hnat : (3347511341 : ℕ)^9*20000000000000^7 ≤ 11939796382997^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347511341 5000000000 11939796382997 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273362043/5000000000 : ℝ)^9 ≤ (18149647916887/50000000000000 : ℝ)^7 := by
    have hnat : (2273362043 : ℕ)^9*50000000000000^7 ≤ 18149647916887^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273362043 5000000000 18149647916887 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-818198599/10000000000 : ℝ), (-3347511341/5000000000 : ℝ), (-2273362043/5000000000 : ℝ)] ![(7815863743/195312500000 : ℝ), (11939796382997/20000000000000 : ℝ), (18149647916887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-818198599/10000000000 : ℝ)|^9 ≤ (7815863743/195312500000 : ℝ)^7
        have hw : |(-818198599/10000000000 : ℝ)|=(818198599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3347511341/5000000000 : ℝ)|^9 ≤ (11939796382997/20000000000000 : ℝ)^7
        have hw : |(-3347511341/5000000000 : ℝ)|=(3347511341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273362043/5000000000 : ℝ)|^9 ≤ (18149647916887/50000000000000 : ℝ)^7
        have hw : |(-2273362043/5000000000 : ℝ)|=(2273362043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5095637369/10000000000 : ℝ)*x 0 + (-1235777/3906250 : ℝ)*x 1 + (2219690291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5095637369/10000000000 : ℝ)^9 ≤ (10507053777157/25000000000000 : ℝ)^7 := by
    have hnat : (5095637369 : ℕ)^9*25000000000000^7 ≤ 10507053777157^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095637369 10000000000 10507053777157 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235777/3906250 : ℝ)^9 ≤ (22770595050577/100000000000000 : ℝ)^7 := by
    have hnat : (1235777 : ℕ)^9*100000000000000^7 ≤ 22770595050577^7*3906250^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235777 3906250 22770595050577 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219690291/5000000000 : ℝ)^9 ≤ (35201189831009/100000000000000 : ℝ)^7 := by
    have hnat : (2219690291 : ℕ)^9*100000000000000^7 ≤ 35201189831009^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219690291 5000000000 35201189831009 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5095637369/10000000000 : ℝ), (-1235777/3906250 : ℝ), (2219690291/5000000000 : ℝ)] ![(10507053777157/25000000000000 : ℝ), (22770595050577/100000000000000 : ℝ), (35201189831009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5095637369/10000000000 : ℝ)|^9 ≤ (10507053777157/25000000000000 : ℝ)^7
        have hw : |(5095637369/10000000000 : ℝ)|=(5095637369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235777/3906250 : ℝ)|^9 ≤ (22770595050577/100000000000000 : ℝ)^7
        have hw : |(-1235777/3906250 : ℝ)|=(1235777/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219690291/5000000000 : ℝ)|^9 ≤ (35201189831009/100000000000000 : ℝ)^7
        have hw : |(2219690291/5000000000 : ℝ)|=(2219690291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3704654619/5000000000 : ℝ)*x 0 + (-2848135033/10000000000 : ℝ)*x 1 + (-1934225583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3704654619/5000000000 : ℝ)^9 ≤ (68009777754717/100000000000000 : ℝ)^7 := by
    have hnat : (3704654619 : ℕ)^9*100000000000000^7 ≤ 68009777754717^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704654619 5000000000 68009777754717 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848135033/10000000000 : ℝ)^9 ≤ (4973484273209/25000000000000 : ℝ)^7 := by
    have hnat : (2848135033 : ℕ)^9*25000000000000^7 ≤ 4973484273209^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848135033 10000000000 4973484273209 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934225583/10000000000 : ℝ)^9 ≤ (3024071283753/25000000000000 : ℝ)^7 := by
    have hnat : (1934225583 : ℕ)^9*25000000000000^7 ≤ 3024071283753^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934225583 10000000000 3024071283753 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3704654619/5000000000 : ℝ), (-2848135033/10000000000 : ℝ), (-1934225583/10000000000 : ℝ)] ![(68009777754717/100000000000000 : ℝ), (4973484273209/25000000000000 : ℝ), (3024071283753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3704654619/5000000000 : ℝ)|^9 ≤ (68009777754717/100000000000000 : ℝ)^7
        have hw : |(3704654619/5000000000 : ℝ)|=(3704654619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2848135033/10000000000 : ℝ)|^9 ≤ (4973484273209/25000000000000 : ℝ)^7
        have hw : |(-2848135033/10000000000 : ℝ)|=(2848135033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934225583/10000000000 : ℝ)|^9 ≤ (3024071283753/25000000000000 : ℝ)^7
        have hw : |(-1934225583/10000000000 : ℝ)|=(1934225583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-899180513/10000000000 : ℝ)*x 0 + (-7136274909/10000000000 : ℝ)*x 1 + (-3988945673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899180513/10000000000 : ℝ)^9 ≤ (4517997608417/100000000000000 : ℝ)^7 := by
    have hnat : (899180513 : ℕ)^9*100000000000000^7 ≤ 4517997608417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899180513 10000000000 4517997608417 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7136274909/10000000000 : ℝ)^9 ≤ (64804670493829/100000000000000 : ℝ)^7 := by
    have hnat : (7136274909 : ℕ)^9*100000000000000^7 ≤ 64804670493829^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7136274909 10000000000 64804670493829 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3988945673/10000000000 : ℝ)^9 ≤ (1917333242859/6250000000000 : ℝ)^7 := by
    have hnat : (3988945673 : ℕ)^9*6250000000000^7 ≤ 1917333242859^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3988945673 10000000000 1917333242859 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899180513/10000000000 : ℝ), (-7136274909/10000000000 : ℝ), (-3988945673/10000000000 : ℝ)] ![(4517997608417/100000000000000 : ℝ), (64804670493829/100000000000000 : ℝ), (1917333242859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899180513/10000000000 : ℝ)|^9 ≤ (4517997608417/100000000000000 : ℝ)^7
        have hw : |(-899180513/10000000000 : ℝ)|=(899180513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7136274909/10000000000 : ℝ)|^9 ≤ (64804670493829/100000000000000 : ℝ)^7
        have hw : |(-7136274909/10000000000 : ℝ)|=(7136274909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3988945673/10000000000 : ℝ)|^9 ≤ (1917333242859/6250000000000 : ℝ)^7
        have hw : |(-3988945673/10000000000 : ℝ)|=(3988945673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2386133751/5000000000 : ℝ)*x 0 + (821182993/2000000000 : ℝ)*x 1 + (-387248731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2386133751/5000000000 : ℝ)^9 ≤ (38630636083641/100000000000000 : ℝ)^7 := by
    have hnat : (2386133751 : ℕ)^9*100000000000000^7 ≤ 38630636083641^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386133751 5000000000 38630636083641 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821182993/2000000000 : ℝ)^9 ≤ (31838723760787/100000000000000 : ℝ)^7 := by
    have hnat : (821182993 : ℕ)^9*100000000000000^7 ≤ 31838723760787^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821182993 2000000000 31838723760787 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387248731/1000000000 : ℝ)^9 ≤ (29530640140709/100000000000000 : ℝ)^7 := by
    have hnat : (387248731 : ℕ)^9*100000000000000^7 ≤ 29530640140709^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387248731 1000000000 29530640140709 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2386133751/5000000000 : ℝ), (821182993/2000000000 : ℝ), (-387248731/1000000000 : ℝ)] ![(38630636083641/100000000000000 : ℝ), (31838723760787/100000000000000 : ℝ), (29530640140709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2386133751/5000000000 : ℝ)|^9 ≤ (38630636083641/100000000000000 : ℝ)^7
        have hw : |(2386133751/5000000000 : ℝ)|=(2386133751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(821182993/2000000000 : ℝ)|^9 ≤ (31838723760787/100000000000000 : ℝ)^7
        have hw : |(821182993/2000000000 : ℝ)|=(821182993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387248731/1000000000 : ℝ)|^9 ≤ (29530640140709/100000000000000 : ℝ)^7
        have hw : |(-387248731/1000000000 : ℝ)|=(387248731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2386133863/5000000000 : ℝ)*x 0 + (-2307023387/10000000000 : ℝ)*x 1 + (5484544371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2386133863/5000000000 : ℝ)^9 ≤ (9657659603737/25000000000000 : ℝ)^7 := by
    have hnat : (2386133863 : ℕ)^9*25000000000000^7 ≤ 9657659603737^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386133863 5000000000 9657659603737 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307023387/10000000000 : ℝ)^9 ≤ (15172839136927/100000000000000 : ℝ)^7 := by
    have hnat : (2307023387 : ℕ)^9*100000000000000^7 ≤ 15172839136927^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307023387 10000000000 15172839136927 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484544371/10000000000 : ℝ)^9 ≤ (46196522440239/100000000000000 : ℝ)^7 := by
    have hnat : (5484544371 : ℕ)^9*100000000000000^7 ≤ 46196522440239^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484544371 10000000000 46196522440239 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2386133863/5000000000 : ℝ), (-2307023387/10000000000 : ℝ), (5484544371/10000000000 : ℝ)] ![(9657659603737/25000000000000 : ℝ), (15172839136927/100000000000000 : ℝ), (46196522440239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2386133863/5000000000 : ℝ)|^9 ≤ (9657659603737/25000000000000 : ℝ)^7
        have hw : |(2386133863/5000000000 : ℝ)|=(2386133863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2307023387/10000000000 : ℝ)|^9 ≤ (15172839136927/100000000000000 : ℝ)^7
        have hw : |(-2307023387/10000000000 : ℝ)|=(2307023387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484544371/10000000000 : ℝ)|^9 ≤ (46196522440239/100000000000000 : ℝ)^7
        have hw : |(5484544371/10000000000 : ℝ)|=(5484544371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7565579133/10000000000 : ℝ)*x 0 + (-2064454131/10000000000 : ℝ)*x 1 + (-251886507/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7565579133/10000000000 : ℝ)^9 ≤ (1746488242721/2500000000000 : ℝ)^7 := by
    have hnat : (7565579133 : ℕ)^9*2500000000000^7 ≤ 1746488242721^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7565579133 10000000000 1746488242721 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064454131/10000000000 : ℝ)^9 ≤ (13153317576827/100000000000000 : ℝ)^7 := by
    have hnat : (2064454131 : ℕ)^9*100000000000000^7 ≤ 13153317576827^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064454131 10000000000 13153317576827 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251886507/1000000000 : ℝ)^9 ≤ (1698715270113/10000000000000 : ℝ)^7 := by
    have hnat : (251886507 : ℕ)^9*10000000000000^7 ≤ 1698715270113^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251886507 1000000000 1698715270113 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7565579133/10000000000 : ℝ), (-2064454131/10000000000 : ℝ), (-251886507/1000000000 : ℝ)] ![(1746488242721/2500000000000 : ℝ), (13153317576827/100000000000000 : ℝ), (1698715270113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7565579133/10000000000 : ℝ)|^9 ≤ (1746488242721/2500000000000 : ℝ)^7
        have hw : |(7565579133/10000000000 : ℝ)|=(7565579133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064454131/10000000000 : ℝ)|^9 ≤ (13153317576827/100000000000000 : ℝ)^7
        have hw : |(-2064454131/10000000000 : ℝ)|=(2064454131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251886507/1000000000 : ℝ)|^9 ≤ (1698715270113/10000000000000 : ℝ)^7
        have hw : |(-251886507/1000000000 : ℝ)|=(251886507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-11843057/10000000000 : ℝ)*x 0 + (-3367360207/5000000000 : ℝ)*x 1 + (-610868281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11843057/10000000000 : ℝ)^9 ≤ (17270727231/100000000000000 : ℝ)^7 := by
    have hnat : (11843057 : ℕ)^9*100000000000000^7 ≤ 17270727231^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11843057 10000000000 17270727231 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3367360207/5000000000 : ℝ)^9 ≤ (12030897192101/20000000000000 : ℝ)^7 := by
    have hnat : (3367360207 : ℕ)^9*20000000000000^7 ≤ 12030897192101^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3367360207 5000000000 12030897192101 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610868281/1250000000 : ℝ)^9 ≤ (39828243296029/100000000000000 : ℝ)^7 := by
    have hnat : (610868281 : ℕ)^9*100000000000000^7 ≤ 39828243296029^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610868281 1250000000 39828243296029 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11843057/10000000000 : ℝ), (-3367360207/5000000000 : ℝ), (-610868281/1250000000 : ℝ)] ![(17270727231/100000000000000 : ℝ), (12030897192101/20000000000000 : ℝ), (39828243296029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11843057/10000000000 : ℝ)|^9 ≤ (17270727231/100000000000000 : ℝ)^7
        have hw : |(-11843057/10000000000 : ℝ)|=(11843057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3367360207/5000000000 : ℝ)|^9 ≤ (12030897192101/20000000000000 : ℝ)^7
        have hw : |(-3367360207/5000000000 : ℝ)|=(3367360207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-610868281/1250000000 : ℝ)|^9 ≤ (39828243296029/100000000000000 : ℝ)^7
        have hw : |(-610868281/1250000000 : ℝ)|=(610868281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4439180827/10000000000 : ℝ)*x 0 + (63214409/200000000 : ℝ)*x 1 + (-5098332291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4439180827/10000000000 : ℝ)^9 ≤ (35199153378429/100000000000000 : ℝ)^7 := by
    have hnat : (4439180827 : ℕ)^9*100000000000000^7 ≤ 35199153378429^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439180827 10000000000 35199153378429 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63214409/200000000 : ℝ)^9 ≤ (22744051250747/100000000000000 : ℝ)^7 := by
    have hnat : (63214409 : ℕ)^9*100000000000000^7 ≤ 22744051250747^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63214409 200000000 22744051250747 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098332291/10000000000 : ℝ)^9 ≤ (21028397675533/50000000000000 : ℝ)^7 := by
    have hnat : (5098332291 : ℕ)^9*50000000000000^7 ≤ 21028397675533^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098332291 10000000000 21028397675533 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4439180827/10000000000 : ℝ), (63214409/200000000 : ℝ), (-5098332291/10000000000 : ℝ)] ![(35199153378429/100000000000000 : ℝ), (22744051250747/100000000000000 : ℝ), (21028397675533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4439180827/10000000000 : ℝ)|^9 ≤ (35199153378429/100000000000000 : ℝ)^7
        have hw : |(4439180827/10000000000 : ℝ)|=(4439180827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63214409/200000000 : ℝ)|^9 ≤ (22744051250747/100000000000000 : ℝ)^7
        have hw : |(63214409/200000000 : ℝ)|=(63214409/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5098332291/10000000000 : ℝ)|^9 ≤ (21028397675533/50000000000000 : ℝ)^7
        have hw : |(-5098332291/10000000000 : ℝ)|=(5098332291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5982151253/10000000000 : ℝ)*x 0 + (-2516740421/10000000000 : ℝ)*x 1 + (32476593/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5982151253/10000000000 : ℝ)^9 ≤ (5165380967619/10000000000000 : ℝ)^7 := by
    have hnat : (5982151253 : ℕ)^9*10000000000000^7 ≤ 5165380967619^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5982151253 10000000000 5165380967619 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516740421/10000000000 : ℝ)^9 ≤ (4242183118259/25000000000000 : ℝ)^7 := by
    have hnat : (2516740421 : ℕ)^9*25000000000000^7 ≤ 4242183118259^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516740421 10000000000 4242183118259 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32476593/80000000 : ℝ)^9 ≤ (31377457825203/100000000000000 : ℝ)^7 := by
    have hnat : (32476593 : ℕ)^9*100000000000000^7 ≤ 31377457825203^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32476593 80000000 31377457825203 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5982151253/10000000000 : ℝ), (-2516740421/10000000000 : ℝ), (32476593/80000000 : ℝ)] ![(5165380967619/10000000000000 : ℝ), (4242183118259/25000000000000 : ℝ), (31377457825203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5982151253/10000000000 : ℝ)|^9 ≤ (5165380967619/10000000000000 : ℝ)^7
        have hw : |(5982151253/10000000000 : ℝ)|=(5982151253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2516740421/10000000000 : ℝ)|^9 ≤ (4242183118259/25000000000000 : ℝ)^7
        have hw : |(-2516740421/10000000000 : ℝ)|=(2516740421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32476593/80000000 : ℝ)|^9 ≤ (31377457825203/100000000000000 : ℝ)^7
        have hw : |(32476593/80000000 : ℝ)|=(32476593/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4515740527/5000000000 : ℝ)*x 0 + (-2573921/19531250 : ℝ)*x 1 + (-4781379/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4515740527/5000000000 : ℝ)^9 ≤ (87724051748749/100000000000000 : ℝ)^7 := by
    have hnat : (4515740527 : ℕ)^9*100000000000000^7 ≤ 87724051748749^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515740527 5000000000 87724051748749 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573921/19531250 : ℝ)^9 ≤ (7385809147197/100000000000000 : ℝ)^7 := by
    have hnat : (2573921 : ℕ)^9*100000000000000^7 ≤ 7385809147197^7*19531250^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573921 19531250 7385809147197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4781379/50000000 : ℝ)^9 ≤ (2445069549449/50000000000000 : ℝ)^7 := by
    have hnat : (4781379 : ℕ)^9*50000000000000^7 ≤ 2445069549449^7*50000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781379 50000000 2445069549449 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4515740527/5000000000 : ℝ), (-2573921/19531250 : ℝ), (-4781379/50000000 : ℝ)] ![(87724051748749/100000000000000 : ℝ), (7385809147197/100000000000000 : ℝ), (2445069549449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4515740527/5000000000 : ℝ)|^9 ≤ (87724051748749/100000000000000 : ℝ)^7
        have hw : |(4515740527/5000000000 : ℝ)|=(4515740527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2573921/19531250 : ℝ)|^9 ≤ (7385809147197/100000000000000 : ℝ)^7
        have hw : |(-2573921/19531250 : ℝ)|=(2573921/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4781379/50000000 : ℝ)|^9 ≤ (2445069549449/50000000000000 : ℝ)^7
        have hw : |(-4781379/50000000 : ℝ)|=(4781379/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-4422607/5000000000 : ℝ)*x 0 + (-922337679/1250000000 : ℝ)*x 1 + (-4156042701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4422607/5000000000 : ℝ)^9 ≤ (1186695513/10000000000000 : ℝ)^7 := by
    have hnat : (4422607 : ℕ)^9*10000000000000^7 ≤ 1186695513^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422607 5000000000 1186695513 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922337679/1250000000 : ℝ)^9 ≤ (6764877236959/10000000000000 : ℝ)^7 := by
    have hnat : (922337679 : ℕ)^9*10000000000000^7 ≤ 6764877236959^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922337679 1250000000 6764877236959 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156042701/10000000000 : ℝ)^9 ≤ (6467872133959/20000000000000 : ℝ)^7 := by
    have hnat : (4156042701 : ℕ)^9*20000000000000^7 ≤ 6467872133959^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156042701 10000000000 6467872133959 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4422607/5000000000 : ℝ), (-922337679/1250000000 : ℝ), (-4156042701/10000000000 : ℝ)] ![(1186695513/10000000000000 : ℝ), (6764877236959/10000000000000 : ℝ), (6467872133959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4422607/5000000000 : ℝ)|^9 ≤ (1186695513/10000000000000 : ℝ)^7
        have hw : |(-4422607/5000000000 : ℝ)|=(4422607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922337679/1250000000 : ℝ)|^9 ≤ (6764877236959/10000000000000 : ℝ)^7
        have hw : |(-922337679/1250000000 : ℝ)|=(922337679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4156042701/10000000000 : ℝ)|^9 ≤ (6467872133959/20000000000000 : ℝ)^7
        have hw : |(-4156042701/10000000000 : ℝ)|=(4156042701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5985149121/10000000000 : ℝ)*x 0 + (284795513/1000000000 : ℝ)*x 1 + (-1879394293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5985149121/10000000000 : ℝ)^9 ≤ (51687093485939/100000000000000 : ℝ)^7 := by
    have hnat : (5985149121 : ℕ)^9*100000000000000^7 ≤ 51687093485939^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5985149121 10000000000 51687093485939 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284795513/1000000000 : ℝ)^9 ≤ (2486540184151/12500000000000 : ℝ)^7 := by
    have hnat : (284795513 : ℕ)^9*12500000000000^7 ≤ 2486540184151^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284795513 1000000000 2486540184151 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879394293/5000000000 : ℝ)^9 ≤ (14210292514887/50000000000000 : ℝ)^7 := by
    have hnat : (1879394293 : ℕ)^9*50000000000000^7 ≤ 14210292514887^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879394293 5000000000 14210292514887 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5985149121/10000000000 : ℝ), (284795513/1000000000 : ℝ), (-1879394293/5000000000 : ℝ)] ![(51687093485939/100000000000000 : ℝ), (2486540184151/12500000000000 : ℝ), (14210292514887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5985149121/10000000000 : ℝ)|^9 ≤ (51687093485939/100000000000000 : ℝ)^7
        have hw : |(5985149121/10000000000 : ℝ)|=(5985149121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284795513/1000000000 : ℝ)|^9 ≤ (2486540184151/12500000000000 : ℝ)^7
        have hw : |(284795513/1000000000 : ℝ)|=(284795513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1879394293/5000000000 : ℝ)|^9 ≤ (14210292514887/50000000000000 : ℝ)^7
        have hw : |(-1879394293/5000000000 : ℝ)|=(1879394293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2235116283/5000000000 : ℝ)*x 0 + (-55702877/156250000 : ℝ)*x 1 + (4705137911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2235116283/5000000000 : ℝ)^9 ≤ (35516031913269/100000000000000 : ℝ)^7 := by
    have hnat : (2235116283 : ℕ)^9*100000000000000^7 ≤ 35516031913269^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235116283 5000000000 35516031913269 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55702877/156250000 : ℝ)^9 ≤ (26550582764849/100000000000000 : ℝ)^7 := by
    have hnat : (55702877 : ℕ)^9*100000000000000^7 ≤ 26550582764849^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55702877 156250000 26550582764849 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4705137911/10000000000 : ℝ)^9 ≤ (9483346327571/25000000000000 : ℝ)^7 := by
    have hnat : (4705137911 : ℕ)^9*25000000000000^7 ≤ 9483346327571^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705137911 10000000000 9483346327571 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2235116283/5000000000 : ℝ), (-55702877/156250000 : ℝ), (4705137911/10000000000 : ℝ)] ![(35516031913269/100000000000000 : ℝ), (26550582764849/100000000000000 : ℝ), (9483346327571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2235116283/5000000000 : ℝ)|^9 ≤ (35516031913269/100000000000000 : ℝ)^7
        have hw : |(2235116283/5000000000 : ℝ)|=(2235116283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55702877/156250000 : ℝ)|^9 ≤ (26550582764849/100000000000000 : ℝ)^7
        have hw : |(-55702877/156250000 : ℝ)|=(55702877/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4705137911/10000000000 : ℝ)|^9 ≤ (9483346327571/25000000000000 : ℝ)^7
        have hw : |(4705137911/10000000000 : ℝ)|=(4705137911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8962053661/10000000000 : ℝ)*x 0 + (-1522422409/10000000000 : ℝ)*x 1 + (-857502177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8962053661/10000000000 : ℝ)^9 ≤ (86857973838763/100000000000000 : ℝ)^7 := by
    have hnat : (8962053661 : ℕ)^9*100000000000000^7 ≤ 86857973838763^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8962053661 10000000000 86857973838763 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522422409/10000000000 : ℝ)^9 ≤ (8891474498299/100000000000000 : ℝ)^7 := by
    have hnat : (1522422409 : ℕ)^9*100000000000000^7 ≤ 8891474498299^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522422409 10000000000 8891474498299 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857502177/10000000000 : ℝ)^9 ≤ (212527582283/5000000000000 : ℝ)^7 := by
    have hnat : (857502177 : ℕ)^9*5000000000000^7 ≤ 212527582283^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857502177 10000000000 212527582283 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8962053661/10000000000 : ℝ), (-1522422409/10000000000 : ℝ), (-857502177/10000000000 : ℝ)] ![(86857973838763/100000000000000 : ℝ), (8891474498299/100000000000000 : ℝ), (212527582283/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8962053661/10000000000 : ℝ)|^9 ≤ (86857973838763/100000000000000 : ℝ)^7
        have hw : |(8962053661/10000000000 : ℝ)|=(8962053661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1522422409/10000000000 : ℝ)|^9 ≤ (8891474498299/100000000000000 : ℝ)^7
        have hw : |(-1522422409/10000000000 : ℝ)|=(1522422409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857502177/10000000000 : ℝ)|^9 ≤ (212527582283/5000000000000 : ℝ)^7
        have hw : |(-857502177/10000000000 : ℝ)|=(857502177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-236767703/1000000000 : ℝ)*x 0 + (-5720602797/10000000000 : ℝ)*x 1 + (-2236478289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236767703/1000000000 : ℝ)^9 ≤ (7843817021749/50000000000000 : ℝ)^7 := by
    have hnat : (236767703 : ℕ)^9*50000000000000^7 ≤ 7843817021749^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236767703 1000000000 7843817021749 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720602797/10000000000 : ℝ)^9 ≤ (48768505795699/100000000000000 : ℝ)^7 := by
    have hnat : (5720602797 : ℕ)^9*100000000000000^7 ≤ 48768505795699^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720602797 10000000000 48768505795699 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236478289/5000000000 : ℝ)^9 ≤ (17771930072289/50000000000000 : ℝ)^7 := by
    have hnat : (2236478289 : ℕ)^9*50000000000000^7 ≤ 17771930072289^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236478289 5000000000 17771930072289 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236767703/1000000000 : ℝ), (-5720602797/10000000000 : ℝ), (-2236478289/5000000000 : ℝ)] ![(7843817021749/50000000000000 : ℝ), (48768505795699/100000000000000 : ℝ), (17771930072289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236767703/1000000000 : ℝ)|^9 ≤ (7843817021749/50000000000000 : ℝ)^7
        have hw : |(-236767703/1000000000 : ℝ)|=(236767703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5720602797/10000000000 : ℝ)|^9 ≤ (48768505795699/100000000000000 : ℝ)^7
        have hw : |(-5720602797/10000000000 : ℝ)|=(5720602797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236478289/5000000000 : ℝ)|^9 ≤ (17771930072289/50000000000000 : ℝ)^7
        have hw : |(-2236478289/5000000000 : ℝ)|=(2236478289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4784697603/10000000000 : ℝ)*x 0 + (3572621049/10000000000 : ℝ)*x 1 + (-219094717/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4784697603/10000000000 : ℝ)^9 ≤ (2422503249681/6250000000000 : ℝ)^7 := by
    have hnat : (4784697603 : ℕ)^9*6250000000000^7 ≤ 2422503249681^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784697603 10000000000 2422503249681 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3572621049/10000000000 : ℝ)^9 ≤ (532474647593/2000000000000 : ℝ)^7 := by
    have hnat : (3572621049 : ℕ)^9*2000000000000^7 ≤ 532474647593^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3572621049 10000000000 532474647593 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219094717/500000000 : ℝ)^9 ≤ (17308107809291/50000000000000 : ℝ)^7 := by
    have hnat : (219094717 : ℕ)^9*50000000000000^7 ≤ 17308107809291^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219094717 500000000 17308107809291 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4784697603/10000000000 : ℝ), (3572621049/10000000000 : ℝ), (-219094717/500000000 : ℝ)] ![(2422503249681/6250000000000 : ℝ), (532474647593/2000000000000 : ℝ), (17308107809291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4784697603/10000000000 : ℝ)|^9 ≤ (2422503249681/6250000000000 : ℝ)^7
        have hw : |(4784697603/10000000000 : ℝ)|=(4784697603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3572621049/10000000000 : ℝ)|^9 ≤ (532474647593/2000000000000 : ℝ)^7
        have hw : |(3572621049/10000000000 : ℝ)|=(3572621049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219094717/500000000 : ℝ)|^9 ≤ (17308107809291/50000000000000 : ℝ)^7
        have hw : |(-219094717/500000000 : ℝ)|=(219094717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4776883213/10000000000 : ℝ)*x 0 + (-3576312623/10000000000 : ℝ)*x 1 + (1096605533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4776883213/10000000000 : ℝ)^9 ≤ (38678681299273/100000000000000 : ℝ)^7 := by
    have hnat : (4776883213 : ℕ)^9*100000000000000^7 ≤ 38678681299273^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776883213 10000000000 38678681299273 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3576312623/10000000000 : ℝ)^9 ≤ (26659107841761/100000000000000 : ℝ)^7 := by
    have hnat : (3576312623 : ℕ)^9*100000000000000^7 ≤ 26659107841761^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576312623 10000000000 26659107841761 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096605533/2500000000 : ℝ)^9 ≤ (6932442167931/20000000000000 : ℝ)^7 := by
    have hnat : (1096605533 : ℕ)^9*20000000000000^7 ≤ 6932442167931^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096605533 2500000000 6932442167931 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4776883213/10000000000 : ℝ), (-3576312623/10000000000 : ℝ), (1096605533/2500000000 : ℝ)] ![(38678681299273/100000000000000 : ℝ), (26659107841761/100000000000000 : ℝ), (6932442167931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4776883213/10000000000 : ℝ)|^9 ≤ (38678681299273/100000000000000 : ℝ)^7
        have hw : |(4776883213/10000000000 : ℝ)|=(4776883213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3576312623/10000000000 : ℝ)|^9 ≤ (26659107841761/100000000000000 : ℝ)^7
        have hw : |(-3576312623/10000000000 : ℝ)|=(3576312623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096605533/2500000000 : ℝ)|^9 ≤ (6932442167931/20000000000000 : ℝ)^7
        have hw : |(1096605533/2500000000 : ℝ)|=(1096605533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310044_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5872087163/10000000000 : ℝ)*x 0 + (-756876373/2000000000 : ℝ)*x 1 + (-2959019593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5872087163/10000000000 : ℝ)^9 ≤ (25217568558397/50000000000000 : ℝ)^7 := by
    have hnat : (5872087163 : ℕ)^9*50000000000000^7 ≤ 25217568558397^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872087163 10000000000 25217568558397 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756876373/2000000000 : ℝ)^9 ≤ (28669629593629/100000000000000 : ℝ)^7 := by
    have hnat : (756876373 : ℕ)^9*100000000000000^7 ≤ 28669629593629^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756876373 2000000000 28669629593629 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2959019593/10000000000 : ℝ)^9 ≤ (326488019877/1562500000000 : ℝ)^7 := by
    have hnat : (2959019593 : ℕ)^9*1562500000000^7 ≤ 326488019877^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959019593 10000000000 326488019877 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5872087163/10000000000 : ℝ), (-756876373/2000000000 : ℝ), (-2959019593/10000000000 : ℝ)] ![(25217568558397/50000000000000 : ℝ), (28669629593629/100000000000000 : ℝ), (326488019877/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5872087163/10000000000 : ℝ)|^9 ≤ (25217568558397/50000000000000 : ℝ)^7
        have hw : |(5872087163/10000000000 : ℝ)|=(5872087163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-756876373/2000000000 : ℝ)|^9 ≤ (28669629593629/100000000000000 : ℝ)^7
        have hw : |(-756876373/2000000000 : ℝ)|=(756876373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2959019593/10000000000 : ℝ)|^9 ≤ (326488019877/1562500000000 : ℝ)^7
        have hw : |(-2959019593/10000000000 : ℝ)|=(2959019593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310044 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-818198599/10000000000 : ℝ)*X 0 0+(-3347511341/5000000000 : ℝ)*X 0 1+(-2273362043/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5095637369/10000000000 : ℝ)*X 2 0+(-1235777/3906250 : ℝ)*X 2 1+(2219690291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3704654619/5000000000 : ℝ)*X 0 0+(-2848135033/10000000000 : ℝ)*X 0 1+(-1934225583/10000000000 : ℝ)*X 0 2+(3704654619/5000000000 : ℝ)*X 1 0+(-2848135033/10000000000 : ℝ)*X 1 1+(-1934225583/10000000000 : ℝ)*X 1 2+(3704654619/5000000000 : ℝ)*X 2 0+(-2848135033/10000000000 : ℝ)*X 2 1+(-1934225583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-899180513/10000000000 : ℝ)*X 0 0+(-7136274909/10000000000 : ℝ)*X 0 1+(-3988945673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2386133751/5000000000 : ℝ)*X 1 0+(821182993/2000000000 : ℝ)*X 1 1+(-387248731/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2386133863/5000000000 : ℝ)*X 2 0+(-2307023387/10000000000 : ℝ)*X 2 1+(5484544371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7565579133/10000000000 : ℝ)*X 0 0+(-2064454131/10000000000 : ℝ)*X 0 1+(-251886507/1000000000 : ℝ)*X 0 2+(7565579133/10000000000 : ℝ)*X 1 0+(-2064454131/10000000000 : ℝ)*X 1 1+(-251886507/1000000000 : ℝ)*X 1 2+(7565579133/10000000000 : ℝ)*X 2 0+(-2064454131/10000000000 : ℝ)*X 2 1+(-251886507/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-11843057/10000000000 : ℝ)*X 0 0+(-3367360207/5000000000 : ℝ)*X 0 1+(-610868281/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4439180827/10000000000 : ℝ)*X 1 0+(63214409/200000000 : ℝ)*X 1 1+(-5098332291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5982151253/10000000000 : ℝ)*X 2 0+(-2516740421/10000000000 : ℝ)*X 2 1+(32476593/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((4515740527/5000000000 : ℝ)*X 0 0+(-2573921/19531250 : ℝ)*X 0 1+(-4781379/50000000 : ℝ)*X 0 2+(4515740527/5000000000 : ℝ)*X 1 0+(-2573921/19531250 : ℝ)*X 1 1+(-4781379/50000000 : ℝ)*X 1 2+(4515740527/5000000000 : ℝ)*X 2 0+(-2573921/19531250 : ℝ)*X 2 1+(-4781379/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-4422607/5000000000 : ℝ)*X 0 0+(-922337679/1250000000 : ℝ)*X 0 1+(-4156042701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5985149121/10000000000 : ℝ)*X 1 0+(284795513/1000000000 : ℝ)*X 1 1+(-1879394293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2235116283/5000000000 : ℝ)*X 2 0+(-55702877/156250000 : ℝ)*X 2 1+(4705137911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8962053661/10000000000 : ℝ)*X 0 0+(-1522422409/10000000000 : ℝ)*X 0 1+(-857502177/10000000000 : ℝ)*X 0 2+(8962053661/10000000000 : ℝ)*X 1 0+(-1522422409/10000000000 : ℝ)*X 1 1+(-857502177/10000000000 : ℝ)*X 1 2+(8962053661/10000000000 : ℝ)*X 2 0+(-1522422409/10000000000 : ℝ)*X 2 1+(-857502177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1459/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1459/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (63683836719443958853203/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255808037407/500000000000 : ℝ)*(base39) + (234734731789/500000000000 : ℝ)*(base49) + (2618448718617/1000000000000 : ℝ)*(major_s0_0) + (2618448718617/1000000000000 : ℝ)*(major_s0_1) + (2618448718617/1000000000000 : ℝ)*(major_s0_2) + (243076119/1000000000000 : ℝ)*(sp_s0_0) + (17529041/100000000000 : ℝ)*(sp_s0_6) + (904563569057/250000000000 : ℝ)*(sp_s0_7) + (904609590147/250000000000 : ℝ)*(sp_s0_8) + (1809214727879/500000000000 : ℝ)*(sp_s0_9) + (809109513701/500000000000 : ℝ)*(sp_s0_13) + (30256621/500000000000 : ℝ)*(sp_s0_15) + (1521483/1000000000000 : ℝ)*(sp_s0_20) + (8677259/125000000000 : ℝ)*(sp_s0_22) + (404598579453/250000000000 : ℝ)*(f.failure) + (361849887383/100000000000 : ℝ)*(f.sum) + (999762421897651/5000000000000000000000000000 : ℝ)*base62 + (2764960305920297/10000000000000000000000000000 : ℝ)*base65 + (973854616920297/10000000000000000000000000000 : ℝ)*base66 + (4569707058397651/10000000000000000000000000000 : ℝ)*base68 + (98535391238677/5000000000000000000000000000 : ℝ)*base70 + (2249071824079703/10000000000000000000000000000 : ℝ)*base73 + (4405283808397651/10000000000000000000000000000 : ℝ)*base74 + (2433730051602349/10000000000000000000000000000 : ℝ)*base77 + (1784450367920297/5000000000000000000000000000 : ℝ)*base78 + (14229/25000000000000000 : ℝ)*base87 + (14229/25000000000000000 : ℝ)*base89 + (14229/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47667/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-47667/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18230852769924549457197/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (983383/1000000000000 : ℝ)*(base12) + (984883779743/500000000000 : ℝ)*(base39) + (697477945173/500000000000 : ℝ)*(base40) + (711813683357/1000000000000 : ℝ)*(base49) + (2344934453017/500000000000 : ℝ)*(major_s0_0) + (2344934453017/500000000000 : ℝ)*(major_s0_1) + (2344934453017/500000000000 : ℝ)*(major_s0_2) + (90805889/1000000000000 : ℝ)*(sp_s0_0) + (48539837/1000000000000 : ℝ)*(sp_s0_9) + (129619178219/20000000000 : ℝ)*(sp_s0_14) + (810130461677/125000000000 : ℝ)*(sp_s0_15) + (1296200432077/200000000000 : ℝ)*(sp_s0_16) + (362335585133/125000000000 : ℝ)*(sp_s0_19) + (3503403/500000000000 : ℝ)*(sp_s0_21) + (362335585133/125000000000 : ℝ)*(f.failure) + (3240525350111/500000000000 : ℝ)*(f.sum) + (69140353889149/2500000000000000000000000000 : ℝ)*base63 + (774260751569303/5000000000000000000000000000 : ℝ)*base64 + (1242996841569303/5000000000000000000000000000 : ℝ)*base67 + (459492795639149/5000000000000000000000000000 : ℝ)*base69 + (699631034923/2500000000000000000000000000 : ℝ)*base71 + (1167775999430697/5000000000000000000000000000 : ℝ)*base72 + (444562541139149/5000000000000000000000000000 : ℝ)*base75 + (339727531360851/5000000000000000000000000000 : ℝ)*base76 + (261443601569303/2500000000000000000000000000 : ℝ)*base79 + (1531/12500000000000000 : ℝ)*base86 + (1531/12500000000000000 : ℝ)*base88 + (1531/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48487/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48487/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29795835368967210495903/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (867971/100000000000 : ℝ)*(base10) + (2167910915867/1000000000000 : ℝ)*(base39) + (1153928849787/1000000000000 : ℝ)*(base40) + (46984831751/62500000000 : ℝ)*(base49) + (4776696886083/1000000000000 : ℝ)*(major_s0_0) + (4776696886083/1000000000000 : ℝ)*(major_s0_1) + (4776696886083/1000000000000 : ℝ)*(major_s0_2) + (725537/50000000000 : ℝ)*(sp_s0_2) + (16266107/500000000000 : ℝ)*(sp_s0_7) + (1776293/125000000000 : ℝ)*(sp_s0_8) + (3300499900447/500000000000 : ℝ)*(sp_s0_20) + (3300513401237/500000000000 : ℝ)*(sp_s0_21) + (3300513251039/500000000000 : ℝ)*(sp_s0_22) + (369043846619/125000000000 : ℝ)*(sp_s0_25) + (369043846619/125000000000 : ℝ)*(f.failure) + (3300520506409/500000000000 : ℝ)*(f.sum) + (1523699252203551/5000000000000000000000000000 : ℝ)*base63 + (3568875827427597/10000000000000000000000000000 : ℝ)*base64 + (1142957149427597/10000000000000000000000000000 : ℝ)*base67 + (5763661025203551/10000000000000000000000000000 : ℝ)*base69 + (1111920098887977/5000000000000000000000000000 : ℝ)*base71 + (4928931162572403/10000000000000000000000000000 : ℝ)*base72 + (6190711859203551/10000000000000000000000000000 : ℝ)*base75 + (807747508796449/10000000000000000000000000000 : ℝ)*base76 + (1773949312427597/5000000000000000000000000000 : ℝ)*base79 + (9633/12500000000000000 : ℝ)*base86 + (9633/12500000000000000 : ℝ)*base88 + (9633/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (1459/12500 : ℝ) ^ (35/8 : ℝ) ≤ (4146967191295869/50000000000000000000 : ℝ) := by
    have hpowers : (1459/12500 : ℝ)^35 ≤ (4146967191295869/50000000000000000000 : ℝ)^8 := by
      have hnat : (1459 : ℕ)^35*50000000000000000000^8 ≤ 4146967191295869^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1459 12500 4146967191295869 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1459/12500 : ℝ)) (X := (4146967191295869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50004146967191295869/50000000000000000000 : ℝ) ≤ (2000037913915727/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50004146967191295869/50000000000000000000 : ℝ)^8 ≤ (2000037913915727/2000000000000000 : ℝ)^35 := by
      have hnat : (50004146967191295869 : ℕ)^8*2000000000000000^35 ≤ 2000037913915727^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004146967191295869 50000000000000000000 2000037913915727 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000037913915727/2000000000000000 : ℝ)) (X := (50004146967191295869/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25004146967191295869/25000000000000000000 : ℝ) ≤ (312511847719677/312500000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25004146967191295869/25000000000000000000 : ℝ)^8 ≤ (312511847719677/312500000000000 : ℝ)^35 := by
      have hnat : (25004146967191295869 : ℕ)^8*312500000000000^35 ≤ 312511847719677^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004146967191295869 25000000000000000000 312511847719677 312500000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312511847719677/312500000000000 : ℝ)) (X := (25004146967191295869/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(37913915727/233440000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(189557451029/1167200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1459/12500 : ℝ)) (alpha := (37913915727/233440000000000 : ℝ)) (beta := (189557451029/1167200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1459/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(37913915727/233440000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(189557451029/1167200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (47667/100000 : ℝ) ^ (35/8 : ℝ) ≤ (3910235925005042277/100000000000000000000 : ℝ) := by
    have hpowers : (47667/100000 : ℝ)^35 ≤ (3910235925005042277/100000000000000000000 : ℝ)^8 := by
      have hnat : (47667 : ℕ)^35*100000000000000000000^8 ≤ 3910235925005042277^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47667 100000 3910235925005042277 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47667/100000 : ℝ)) (X := (3910235925005042277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (103910235925005042277/100000000000000000000 : ℝ) ≤ (10088059114811841/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (103910235925005042277/100000000000000000000 : ℝ)^8 ≤ (10088059114811841/10000000000000000 : ℝ)^35 := by
      have hnat : (103910235925005042277 : ℕ)^8*10000000000000000^35 ≤ 10088059114811841^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103910235925005042277 100000000000000000000 10088059114811841 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10088059114811841/10000000000000000 : ℝ)) (X := (103910235925005042277/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53910235925005042277/50000000000000000000 : ℝ) ≤ (635849865505883/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (53910235925005042277/50000000000000000000 : ℝ)^8 ≤ (635849865505883/625000000000000 : ℝ)^35 := by
      have hnat : (53910235925005042277 : ℕ)^8*625000000000000^35 ≤ 635849865505883^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53910235925005042277 50000000000000000000 635849865505883 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (635849865505883/625000000000000 : ℝ)) (X := (53910235925005042277/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(88059114811841/4766700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(85538733282287/4766700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (47667/100000 : ℝ)) (alpha := (88059114811841/4766700000000000 : ℝ)) (beta := (85538733282287/4766700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (47667/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(88059114811841/4766700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(85538733282287/4766700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48487/100000 : ℝ) ^ (35/8 : ℝ) ≤ (4213187135892589459/100000000000000000000 : ℝ) := by
    have hpowers : (48487/100000 : ℝ)^35 ≤ (4213187135892589459/100000000000000000000 : ℝ)^8 := by
      have hnat : (48487 : ℕ)^35*100000000000000000000^8 ≤ 4213187135892589459^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48487 100000 4213187135892589459 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48487/100000 : ℝ)) (X := (4213187135892589459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (104213187135892589459/100000000000000000000 : ℝ) ≤ (10094774270728229/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (104213187135892589459/100000000000000000000 : ℝ)^8 ≤ (10094774270728229/10000000000000000 : ℝ)^35 := by
      have hnat : (104213187135892589459 : ℕ)^8*10000000000000000^35 ≤ 10094774270728229^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104213187135892589459 100000000000000000000 10094774270728229 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10094774270728229/10000000000000000 : ℝ)) (X := (104213187135892589459/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (54213187135892589459/50000000000000000000 : ℝ) ≤ (254665932033303/250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (54213187135892589459/50000000000000000000 : ℝ)^8 ≤ (254665932033303/250000000000000 : ℝ)^35 := by
      have hnat : (54213187135892589459 : ℕ)^8*250000000000000^35 ≤ 254665932033303^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54213187135892589459 50000000000000000000 254665932033303 250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (254665932033303/250000000000000 : ℝ)) (X := (54213187135892589459/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(94774270728229/4848700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(91863010603891/4848700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (48487/100000 : ℝ)) (alpha := (94774270728229/4848700000000000 : ℝ)) (beta := (91863010603891/4848700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48487/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(94774270728229/4848700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(91863010603891/4848700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-236767703/1000000000 : ℝ)*X 0 0+(-5720602797/10000000000 : ℝ)*X 0 1+(-2236478289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4784697603/10000000000 : ℝ)*X 1 0+(3572621049/10000000000 : ℝ)*X 1 1+(-219094717/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4776883213/10000000000 : ℝ)*X 2 0+(-3576312623/10000000000 : ℝ)*X 2 1+(1096605533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5872087163/10000000000 : ℝ)*X 0 0+(-756876373/2000000000 : ℝ)*X 0 1+(-2959019593/10000000000 : ℝ)*X 0 2+(5872087163/10000000000 : ℝ)*X 1 0+(-756876373/2000000000 : ℝ)*X 1 1+(-2959019593/10000000000 : ℝ)*X 1 2+(5872087163/10000000000 : ℝ)*X 2 0+(-756876373/2000000000 : ℝ)*X 2 1+(-2959019593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-374351734359258774783128336110908051/56201405341850000000000000000000000 : ℝ) := by norm_num
    linear_combination (287467/500000000000 : ℝ)*(base10) + (8021/62500000000 : ℝ)*(base12) + (258531/1000000000000 : ℝ)*(base25) + (158806928837/200000000000 : ℝ)*(base39) + (445180801481/1000000000000 : ℝ)*(base40) + (1857/15625000000 : ℝ)*(base43) + (299864448011/1000000000000 : ℝ)*(base49) + (12011/250000000000 : ℝ)*(ratio_s0_2) + (161793/100000 : ℝ)*(major_s1_0) + (25280154393/15625000000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2220297953223/1000000000000 : ℝ)*(sp_s1_0) + (2220298775341/1000000000000 : ℝ)*(sp_s1_1) + (2220298397963/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2220298775341/1000000000000 : ℝ)*(f.sum) + (2208076157940297393/19260248575000000000000000000000 : ℝ)*base62 + (187803070088003/484870000000000000000000000 : ℝ)*base64 + (18472450616467/397225000000000000000000000 : ℝ)*base67 + (6174463983599/484870000000000000000000000 : ℝ)*base69 + (84665386546646897/707425330000000000000000000000 : ℝ)*base70 + (145674803373/729500000000000000000000 : ℝ)*base73 + (123271254675483/794450000000000000000000000 : ℝ)*base74 + (3678780066409/14590000000000000000000000 : ℝ)*base76 + (25703461646133289/289775637500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b025 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=44 ∨ c=45 := by omega
  rcases hc with rfl|rfl
  · exact collision_c310044 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310045 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
