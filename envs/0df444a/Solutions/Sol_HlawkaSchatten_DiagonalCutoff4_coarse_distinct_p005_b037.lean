-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b037
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:28:27.959928+00:00
-- url     : https://prove2.me/submissions/43244e9c-2a39-41b9-b8a7-e74abae27ec3

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s4
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305086_s5
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c305086 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c305086_s0 p hpa hpb X hX
  have h1 := collision_c305086_s1 p hpa hpb X hX h0
  have h2 := collision_c305086_s2 p hpa hpb X hX h1
  have h3 := collision_c305086_s3 p hpa hpb X hX h2
  have h4 := collision_c305086_s4 p hpa hpb X hX h3
  exact collision_c305086_s5 p hpa hpb X hX h4

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
theorem collision_support_c305085_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001234149/5000000000 : ℝ)*x 0 + (-1872767423/2500000000 : ℝ)*x 1 + (2880003589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001234149/5000000000 : ℝ)^67 ≤ (12090631649457/100000000000000 : ℝ)^51 := by
    have hnat : (1001234149 : ℕ)^67*100000000000000^51 ≤ 12090631649457^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001234149 5000000000 12090631649457 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872767423/2500000000 : ℝ)^67 ≤ (8552538825493/12500000000000 : ℝ)^51 := by
    have hnat : (1872767423 : ℕ)^67*12500000000000^51 ≤ 8552538825493^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872767423 2500000000 8552538825493 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2880003589/10000000000 : ℝ)^67 ≤ (19489057726087/100000000000000 : ℝ)^51 := by
    have hnat : (2880003589 : ℕ)^67*100000000000000^51 ≤ 19489057726087^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2880003589 10000000000 19489057726087 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001234149/5000000000 : ℝ), (-1872767423/2500000000 : ℝ), (2880003589/10000000000 : ℝ)] ![(12090631649457/100000000000000 : ℝ), (8552538825493/12500000000000 : ℝ), (19489057726087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001234149/5000000000 : ℝ)|^67 ≤ (12090631649457/100000000000000 : ℝ)^51
        have hw : |(-1001234149/5000000000 : ℝ)|=(1001234149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872767423/2500000000 : ℝ)|^67 ≤ (8552538825493/12500000000000 : ℝ)^51
        have hw : |(-1872767423/2500000000 : ℝ)|=(1872767423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2880003589/10000000000 : ℝ)|^67 ≤ (19489057726087/100000000000000 : ℝ)^51
        have hw : |(2880003589/10000000000 : ℝ)|=(2880003589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5618152077/10000000000 : ℝ)*x 0 + (354296501/1250000000 : ℝ)*x 1 + (4402113133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5618152077/10000000000 : ℝ)^67 ≤ (2344253593441/5000000000000 : ℝ)^51 := by
    have hnat : (5618152077 : ℕ)^67*5000000000000^51 ≤ 2344253593441^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618152077 10000000000 2344253593441 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354296501/1250000000 : ℝ)^67 ≤ (3816880849507/20000000000000 : ℝ)^51 := by
    have hnat : (354296501 : ℕ)^67*20000000000000^51 ≤ 3816880849507^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354296501 1250000000 3816880849507 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402113133/10000000000 : ℝ)^67 ≤ (4253815484137/12500000000000 : ℝ)^51 := by
    have hnat : (4402113133 : ℕ)^67*12500000000000^51 ≤ 4253815484137^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402113133 10000000000 4253815484137 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5618152077/10000000000 : ℝ), (354296501/1250000000 : ℝ), (4402113133/10000000000 : ℝ)] ![(2344253593441/5000000000000 : ℝ), (3816880849507/20000000000000 : ℝ), (4253815484137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5618152077/10000000000 : ℝ)|^67 ≤ (2344253593441/5000000000000 : ℝ)^51
        have hw : |(5618152077/10000000000 : ℝ)|=(5618152077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354296501/1250000000 : ℝ)|^67 ≤ (3816880849507/20000000000000 : ℝ)^51
        have hw : |(354296501/1250000000 : ℝ)|=(354296501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402113133/10000000000 : ℝ)|^67 ≤ (4253815484137/12500000000000 : ℝ)^51
        have hw : |(4402113133/10000000000 : ℝ)|=(4402113133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (675826119/1000000000 : ℝ)*x 0 + (-229776953/1000000000 : ℝ)*x 1 + (445026807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675826119/1000000000 : ℝ)^67 ≤ (29882702400173/50000000000000 : ℝ)^51 := by
    have hnat : (675826119 : ℕ)^67*50000000000000^51 ≤ 29882702400173^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675826119 1000000000 29882702400173 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229776953/1000000000 : ℝ)^67 ≤ (724272554529/5000000000000 : ℝ)^51 := by
    have hnat : (229776953 : ℕ)^67*5000000000000^51 ≤ 724272554529^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229776953 1000000000 724272554529 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445026807/1250000000 : ℝ)^67 ≤ (6437286021893/25000000000000 : ℝ)^51 := by
    have hnat : (445026807 : ℕ)^67*25000000000000^51 ≤ 6437286021893^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445026807 1250000000 6437286021893 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675826119/1000000000 : ℝ), (-229776953/1000000000 : ℝ), (445026807/1250000000 : ℝ)] ![(29882702400173/50000000000000 : ℝ), (724272554529/5000000000000 : ℝ), (6437286021893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675826119/1000000000 : ℝ)|^67 ≤ (29882702400173/50000000000000 : ℝ)^51
        have hw : |(675826119/1000000000 : ℝ)|=(675826119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-229776953/1000000000 : ℝ)|^67 ≤ (724272554529/5000000000000 : ℝ)^51
        have hw : |(-229776953/1000000000 : ℝ)|=(229776953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(445026807/1250000000 : ℝ)|^67 ≤ (6437286021893/25000000000000 : ℝ)^51
        have hw : |(445026807/1250000000 : ℝ)|=(445026807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-46642293/312500000 : ℝ)*x 0 + (-2082074089/2500000000 : ℝ)*x 1 + (266739811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46642293/312500000 : ℝ)^67 ≤ (8218084737369/100000000000000 : ℝ)^51 := by
    have hnat : (46642293 : ℕ)^67*100000000000000^51 ≤ 8218084737369^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46642293 312500000 8218084737369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082074089/2500000000 : ℝ)^67 ≤ (2457438388389/3125000000000 : ℝ)^51 := by
    have hnat : (2082074089 : ℕ)^67*3125000000000^51 ≤ 2457438388389^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082074089 2500000000 2457438388389 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266739811/1250000000 : ℝ)^67 ≤ (13143886819013/100000000000000 : ℝ)^51 := by
    have hnat : (266739811 : ℕ)^67*100000000000000^51 ≤ 13143886819013^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266739811 1250000000 13143886819013 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46642293/312500000 : ℝ), (-2082074089/2500000000 : ℝ), (266739811/1250000000 : ℝ)] ![(8218084737369/100000000000000 : ℝ), (2457438388389/3125000000000 : ℝ), (13143886819013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46642293/312500000 : ℝ)|^67 ≤ (8218084737369/100000000000000 : ℝ)^51
        have hw : |(-46642293/312500000 : ℝ)|=(46642293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082074089/2500000000 : ℝ)|^67 ≤ (2457438388389/3125000000000 : ℝ)^51
        have hw : |(-2082074089/2500000000 : ℝ)|=(2082074089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266739811/1250000000 : ℝ)|^67 ≤ (13143886819013/100000000000000 : ℝ)^51
        have hw : |(266739811/1250000000 : ℝ)|=(266739811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (564579453/1000000000 : ℝ)*x 0 + (2659133649/10000000000 : ℝ)*x 1 + (180914501/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564579453/1000000000 : ℝ)^67 ≤ (9437672219021/20000000000000 : ℝ)^51 := by
    have hnat : (564579453 : ℕ)^67*20000000000000^51 ≤ 9437672219021^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564579453 1000000000 9437672219021 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659133649/10000000000 : ℝ)^67 ≤ (17549570497963/100000000000000 : ℝ)^51 := by
    have hnat : (2659133649 : ℕ)^67*100000000000000^51 ≤ 17549570497963^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659133649 10000000000 17549570497963 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180914501/400000000 : ℝ)^67 ≤ (4407758548083/12500000000000 : ℝ)^51 := by
    have hnat : (180914501 : ℕ)^67*12500000000000^51 ≤ 4407758548083^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180914501 400000000 4407758548083 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564579453/1000000000 : ℝ), (2659133649/10000000000 : ℝ), (180914501/400000000 : ℝ)] ![(9437672219021/20000000000000 : ℝ), (17549570497963/100000000000000 : ℝ), (4407758548083/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564579453/1000000000 : ℝ)|^67 ≤ (9437672219021/20000000000000 : ℝ)^51
        have hw : |(564579453/1000000000 : ℝ)|=(564579453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2659133649/10000000000 : ℝ)|^67 ≤ (17549570497963/100000000000000 : ℝ)^51
        have hw : |(2659133649/10000000000 : ℝ)|=(2659133649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180914501/400000000 : ℝ)|^67 ≤ (4407758548083/12500000000000 : ℝ)^51
        have hw : |(180914501/400000000 : ℝ)|=(180914501/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4199371589/10000000000 : ℝ)*x 0 + (-1289295007/5000000000 : ℝ)*x 1 + (-1200776711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199371589/10000000000 : ℝ)^67 ≤ (3998320745111/12500000000000 : ℝ)^51 := by
    have hnat : (4199371589 : ℕ)^67*12500000000000^51 ≤ 3998320745111^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199371589 10000000000 3998320745111 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1289295007/5000000000 : ℝ)^67 ≤ (8427289691187/50000000000000 : ℝ)^51 := by
    have hnat : (1289295007 : ℕ)^67*50000000000000^51 ≤ 8427289691187^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289295007 5000000000 8427289691187 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200776711/2000000000 : ℝ)^67 ≤ (10231770929433/20000000000000 : ℝ)^51 := by
    have hnat : (1200776711 : ℕ)^67*20000000000000^51 ≤ 10231770929433^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200776711 2000000000 10231770929433 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199371589/10000000000 : ℝ), (-1289295007/5000000000 : ℝ), (-1200776711/2000000000 : ℝ)] ![(3998320745111/12500000000000 : ℝ), (8427289691187/50000000000000 : ℝ), (10231770929433/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199371589/10000000000 : ℝ)|^67 ≤ (3998320745111/12500000000000 : ℝ)^51
        have hw : |(4199371589/10000000000 : ℝ)|=(4199371589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1289295007/5000000000 : ℝ)|^67 ≤ (8427289691187/50000000000000 : ℝ)^51
        have hw : |(-1289295007/5000000000 : ℝ)|=(1289295007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1200776711/2000000000 : ℝ)|^67 ≤ (10231770929433/20000000000000 : ℝ)^51
        have hw : |(-1200776711/2000000000 : ℝ)|=(1200776711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_11 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^67 ≤ (1 : ℝ)^51 := by
    have hnat : (1 : ℕ)^67*1^51 ≤ 1^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1 : ℝ)|^67 ≤ (1 : ℝ)^51
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-941007017/5000000000 : ℝ)*x 0 + (-3787303463/5000000000 : ℝ)*x 1 + (2873499387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941007017/5000000000 : ℝ)^67 ≤ (1393039948723/12500000000000 : ℝ)^51 := by
    have hnat : (941007017 : ℕ)^67*12500000000000^51 ≤ 1393039948723^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941007017 5000000000 1393039948723 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3787303463/5000000000 : ℝ)^67 ≤ (13884884924079/20000000000000 : ℝ)^51 := by
    have hnat : (3787303463 : ℕ)^67*20000000000000^51 ≤ 13884884924079^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3787303463 5000000000 13884884924079 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2873499387/10000000000 : ℝ)^67 ≤ (9715627887331/50000000000000 : ℝ)^51 := by
    have hnat : (2873499387 : ℕ)^67*50000000000000^51 ≤ 9715627887331^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2873499387 10000000000 9715627887331 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941007017/5000000000 : ℝ), (-3787303463/5000000000 : ℝ), (2873499387/10000000000 : ℝ)] ![(1393039948723/12500000000000 : ℝ), (13884884924079/20000000000000 : ℝ), (9715627887331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941007017/5000000000 : ℝ)|^67 ≤ (1393039948723/12500000000000 : ℝ)^51
        have hw : |(-941007017/5000000000 : ℝ)|=(941007017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3787303463/5000000000 : ℝ)|^67 ≤ (13884884924079/20000000000000 : ℝ)^51
        have hw : |(-3787303463/5000000000 : ℝ)|=(3787303463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2873499387/10000000000 : ℝ)|^67 ≤ (9715627887331/50000000000000 : ℝ)^51
        have hw : |(2873499387/10000000000 : ℝ)|=(2873499387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2323726547/5000000000 : ℝ)*x 0 + (1469524781/5000000000 : ℝ)*x 1 + (132528473/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2323726547/5000000000 : ℝ)^67 ≤ (1461745865231/4000000000000 : ℝ)^51 := by
    have hnat : (2323726547 : ℕ)^67*4000000000000^51 ≤ 1461745865231^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323726547 5000000000 1461745865231 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1469524781/5000000000 : ℝ)^67 ≤ (10007828770871/50000000000000 : ℝ)^51 := by
    have hnat : (1469524781 : ℕ)^67*50000000000000^51 ≤ 10007828770871^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469524781 5000000000 10007828770871 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132528473/250000000 : ℝ)^67 ≤ (5430086976143/12500000000000 : ℝ)^51 := by
    have hnat : (132528473 : ℕ)^67*12500000000000^51 ≤ 5430086976143^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132528473 250000000 5430086976143 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2323726547/5000000000 : ℝ), (1469524781/5000000000 : ℝ), (132528473/250000000 : ℝ)] ![(1461745865231/4000000000000 : ℝ), (10007828770871/50000000000000 : ℝ), (5430086976143/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2323726547/5000000000 : ℝ)|^67 ≤ (1461745865231/4000000000000 : ℝ)^51
        have hw : |(2323726547/5000000000 : ℝ)|=(2323726547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1469524781/5000000000 : ℝ)|^67 ≤ (10007828770871/50000000000000 : ℝ)^51
        have hw : |(1469524781/5000000000 : ℝ)|=(1469524781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132528473/250000000 : ℝ)|^67 ≤ (5430086976143/12500000000000 : ℝ)^51
        have hw : |(132528473/250000000 : ℝ)|=(132528473/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4198636431/10000000000 : ℝ)*x 0 + (-2879948211/10000000000 : ℝ)*x 1 + (-5767771723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198636431/10000000000 : ℝ)^67 ≤ (15989604853591/50000000000000 : ℝ)^51 := by
    have hnat : (4198636431 : ℕ)^67*50000000000000^51 ≤ 15989604853591^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198636431 10000000000 15989604853591 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2879948211/10000000000 : ℝ)^67 ≤ (19488565416383/100000000000000 : ℝ)^51 := by
    have hnat : (2879948211 : ℕ)^67*100000000000000^51 ≤ 19488565416383^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2879948211 10000000000 19488565416383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5767771723/10000000000 : ℝ)^67 ≤ (24266112430307/50000000000000 : ℝ)^51 := by
    have hnat : (5767771723 : ℕ)^67*50000000000000^51 ≤ 24266112430307^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5767771723 10000000000 24266112430307 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198636431/10000000000 : ℝ), (-2879948211/10000000000 : ℝ), (-5767771723/10000000000 : ℝ)] ![(15989604853591/50000000000000 : ℝ), (19488565416383/100000000000000 : ℝ), (24266112430307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198636431/10000000000 : ℝ)|^67 ≤ (15989604853591/50000000000000 : ℝ)^51
        have hw : |(4198636431/10000000000 : ℝ)|=(4198636431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2879948211/10000000000 : ℝ)|^67 ≤ (19488565416383/100000000000000 : ℝ)^51
        have hw : |(-2879948211/10000000000 : ℝ)|=(2879948211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5767771723/10000000000 : ℝ)|^67 ≤ (24266112430307/50000000000000 : ℝ)^51
        have hw : |(-5767771723/10000000000 : ℝ)|=(5767771723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2125288369/2500000000 : ℝ)*x 0 + (-183633349/1250000000 : ℝ)*x 1 + (376862203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125288369/2500000000 : ℝ)^67 ≤ (5049324479479/6250000000000 : ℝ)^51 := by
    have hnat : (2125288369 : ℕ)^67*6250000000000^51 ≤ 5049324479479^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125288369 2500000000 5049324479479 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183633349/1250000000 : ℝ)^67 ≤ (804861661873/10000000000000 : ℝ)^51 := by
    have hnat : (183633349 : ℕ)^67*10000000000000^51 ≤ 804861661873^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183633349 1250000000 804861661873 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376862203/2000000000 : ℝ)^67 ≤ (5581095850209/50000000000000 : ℝ)^51 := by
    have hnat : (376862203 : ℕ)^67*50000000000000^51 ≤ 5581095850209^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376862203 2000000000 5581095850209 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125288369/2500000000 : ℝ), (-183633349/1250000000 : ℝ), (376862203/2000000000 : ℝ)] ![(5049324479479/6250000000000 : ℝ), (804861661873/10000000000000 : ℝ), (5581095850209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125288369/2500000000 : ℝ)|^67 ≤ (5049324479479/6250000000000 : ℝ)^51
        have hw : |(2125288369/2500000000 : ℝ)|=(2125288369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183633349/1250000000 : ℝ)|^67 ≤ (804861661873/10000000000000 : ℝ)^51
        have hw : |(-183633349/1250000000 : ℝ)|=(183633349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376862203/2000000000 : ℝ)|^67 ≤ (5581095850209/50000000000000 : ℝ)^51
        have hw : |(376862203/2000000000 : ℝ)|=(376862203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232240247/10000000000 : ℝ)*x 0 + (-8303556697/10000000000 : ℝ)*x 1 + (29913443/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232240247/10000000000 : ℝ)^67 ≤ (1277771950883/20000000000000 : ℝ)^51 := by
    have hnat : (1232240247 : ℕ)^67*20000000000000^51 ≤ 1277771950883^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232240247 10000000000 1277771950883 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8303556697/10000000000 : ℝ)^67 ≤ (7833128714617/10000000000000 : ℝ)^51 := by
    have hnat : (8303556697 : ℕ)^67*10000000000000^51 ≤ 7833128714617^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8303556697 10000000000 7833128714617 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29913443/125000000 : ℝ)^67 ≤ (15279853085843/100000000000000 : ℝ)^51 := by
    have hnat : (29913443 : ℕ)^67*100000000000000^51 ≤ 15279853085843^51*125000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29913443 125000000 15279853085843 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232240247/10000000000 : ℝ), (-8303556697/10000000000 : ℝ), (29913443/125000000 : ℝ)] ![(1277771950883/20000000000000 : ℝ), (7833128714617/10000000000000 : ℝ), (15279853085843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232240247/10000000000 : ℝ)|^67 ≤ (1277771950883/20000000000000 : ℝ)^51
        have hw : |(-1232240247/10000000000 : ℝ)|=(1232240247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8303556697/10000000000 : ℝ)|^67 ≤ (7833128714617/10000000000000 : ℝ)^51
        have hw : |(-8303556697/10000000000 : ℝ)|=(8303556697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29913443/125000000 : ℝ)|^67 ≤ (15279853085843/100000000000000 : ℝ)^51
        have hw : |(29913443/125000000 : ℝ)|=(29913443/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (402076997/625000000 : ℝ)*x 0 + (63194411/250000000 : ℝ)*x 1 + (3749481117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402076997/625000000 : ℝ)^67 ≤ (28009062632817/50000000000000 : ℝ)^51 := by
    have hnat : (402076997 : ℕ)^67*50000000000000^51 ≤ 28009062632817^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402076997 625000000 28009062632817 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63194411/250000000 : ℝ)^67 ≤ (8209799670581/50000000000000 : ℝ)^51 := by
    have hnat : (63194411 : ℕ)^67*50000000000000^51 ≤ 8209799670581^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63194411 250000000 8209799670581 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749481117/10000000000 : ℝ)^67 ≤ (27562275376809/100000000000000 : ℝ)^51 := by
    have hnat : (3749481117 : ℕ)^67*100000000000000^51 ≤ 27562275376809^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749481117 10000000000 27562275376809 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402076997/625000000 : ℝ), (63194411/250000000 : ℝ), (3749481117/10000000000 : ℝ)] ![(28009062632817/50000000000000 : ℝ), (8209799670581/50000000000000 : ℝ), (27562275376809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402076997/625000000 : ℝ)|^67 ≤ (28009062632817/50000000000000 : ℝ)^51
        have hw : |(402076997/625000000 : ℝ)|=(402076997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63194411/250000000 : ℝ)|^67 ≤ (8209799670581/50000000000000 : ℝ)^51
        have hw : |(63194411/250000000 : ℝ)|=(63194411/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3749481117/10000000000 : ℝ)|^67 ≤ (27562275376809/100000000000000 : ℝ)^51
        have hw : |(3749481117/10000000000 : ℝ)|=(3749481117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3448696403/10000000000 : ℝ)*x 0 + (-168808093/500000000 : ℝ)*x 1 + (-150390943/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3448696403/10000000000 : ℝ)^67 ≤ (24694801581483/100000000000000 : ℝ)^51 := by
    have hnat : (3448696403 : ℕ)^67*100000000000000^51 ≤ 24694801581483^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448696403 10000000000 24694801581483 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168808093/500000000 : ℝ)^67 ≤ (24014724863581/100000000000000 : ℝ)^51 := by
    have hnat : (168808093 : ℕ)^67*100000000000000^51 ≤ 24014724863581^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168808093 500000000 24014724863581 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150390943/250000000 : ℝ)^67 ≤ (51290473546093/100000000000000 : ℝ)^51 := by
    have hnat : (150390943 : ℕ)^67*100000000000000^51 ≤ 51290473546093^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150390943 250000000 51290473546093 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3448696403/10000000000 : ℝ), (-168808093/500000000 : ℝ), (-150390943/250000000 : ℝ)] ![(24694801581483/100000000000000 : ℝ), (24014724863581/100000000000000 : ℝ), (51290473546093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3448696403/10000000000 : ℝ)|^67 ≤ (24694801581483/100000000000000 : ℝ)^51
        have hw : |(3448696403/10000000000 : ℝ)|=(3448696403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168808093/500000000 : ℝ)|^67 ≤ (24014724863581/100000000000000 : ℝ)^51
        have hw : |(-168808093/500000000 : ℝ)|=(168808093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150390943/250000000 : ℝ)|^67 ≤ (51290473546093/100000000000000 : ℝ)^51
        have hw : |(-150390943/250000000 : ℝ)|=(150390943/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s0_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2102565443/2500000000 : ℝ)*x 0 + (-681226733/10000000000 : ℝ)*x 1 + (33039167/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102565443/2500000000 : ℝ)^67 ≤ (19914084702071/25000000000000 : ℝ)^51 := by
    have hnat : (2102565443 : ℕ)^67*25000000000000^51 ≤ 19914084702071^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102565443 2500000000 19914084702071 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681226733/10000000000 : ℝ)^67 ≤ (1466342924329/50000000000000 : ℝ)^51 := by
    have hnat : (681226733 : ℕ)^67*50000000000000^51 ≤ 1466342924329^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681226733 10000000000 1466342924329 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33039167/125000000 : ℝ)^67 ≤ (17410975324213/100000000000000 : ℝ)^51 := by
    have hnat : (33039167 : ℕ)^67*100000000000000^51 ≤ 17410975324213^51*125000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33039167 125000000 17410975324213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102565443/2500000000 : ℝ), (-681226733/10000000000 : ℝ), (33039167/125000000 : ℝ)] ![(19914084702071/25000000000000 : ℝ), (1466342924329/50000000000000 : ℝ), (17410975324213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102565443/2500000000 : ℝ)|^67 ≤ (19914084702071/25000000000000 : ℝ)^51
        have hw : |(2102565443/2500000000 : ℝ)|=(2102565443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-681226733/10000000000 : ℝ)|^67 ≤ (1466342924329/50000000000000 : ℝ)^51
        have hw : |(-681226733/10000000000 : ℝ)|=(681226733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33039167/125000000 : ℝ)|^67 ≤ (17410975324213/100000000000000 : ℝ)^51
        have hw : |(33039167/125000000 : ℝ)|=(33039167/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-666129131/2000000000 : ℝ)*x 0 + (-2774540083/5000000000 : ℝ)*x 1 + (80555209/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666129131/2000000000 : ℝ)^67 ≤ (5897574523457/25000000000000 : ℝ)^51 := by
    have hnat : (666129131 : ℕ)^67*25000000000000^51 ≤ 5897574523457^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666129131 2000000000 5897574523457 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2774540083/5000000000 : ℝ)^67 ≤ (23064636306671/50000000000000 : ℝ)^51 := by
    have hnat : (2774540083 : ℕ)^67*50000000000000^51 ≤ 23064636306671^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774540083 5000000000 23064636306671 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80555209/200000000 : ℝ)^67 ≤ (3785053660113/12500000000000 : ℝ)^51 := by
    have hnat : (80555209 : ℕ)^67*12500000000000^51 ≤ 3785053660113^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80555209 200000000 3785053660113 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-666129131/2000000000 : ℝ), (-2774540083/5000000000 : ℝ), (80555209/200000000 : ℝ)] ![(5897574523457/25000000000000 : ℝ), (23064636306671/50000000000000 : ℝ), (3785053660113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-666129131/2000000000 : ℝ)|^67 ≤ (5897574523457/25000000000000 : ℝ)^51
        have hw : |(-666129131/2000000000 : ℝ)|=(666129131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2774540083/5000000000 : ℝ)|^67 ≤ (23064636306671/50000000000000 : ℝ)^51
        have hw : |(-2774540083/5000000000 : ℝ)|=(2774540083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80555209/200000000 : ℝ)|^67 ≤ (3785053660113/12500000000000 : ℝ)^51
        have hw : |(80555209/200000000 : ℝ)|=(80555209/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5287337431/10000000000 : ℝ)*x 0 + (3430929381/10000000000 : ℝ)*x 1 + (1054672607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287337431/10000000000 : ℝ)^67 ≤ (21646088637587/50000000000000 : ℝ)^51 := by
    have hnat : (5287337431 : ℕ)^67*50000000000000^51 ≤ 21646088637587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287337431 10000000000 21646088637587 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3430929381/10000000000 : ℝ)^67 ≤ (24527800869793/100000000000000 : ℝ)^51 := by
    have hnat : (3430929381 : ℕ)^67*100000000000000^51 ≤ 24527800869793^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3430929381 10000000000 24527800869793 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054672607/2500000000 : ℝ)^67 ≤ (16090010917389/50000000000000 : ℝ)^51 := by
    have hnat : (1054672607 : ℕ)^67*50000000000000^51 ≤ 16090010917389^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054672607 2500000000 16090010917389 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287337431/10000000000 : ℝ), (3430929381/10000000000 : ℝ), (1054672607/2500000000 : ℝ)] ![(21646088637587/50000000000000 : ℝ), (24527800869793/100000000000000 : ℝ), (16090010917389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287337431/10000000000 : ℝ)|^67 ≤ (21646088637587/50000000000000 : ℝ)^51
        have hw : |(5287337431/10000000000 : ℝ)|=(5287337431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3430929381/10000000000 : ℝ)|^67 ≤ (24527800869793/100000000000000 : ℝ)^51
        have hw : |(3430929381/10000000000 : ℝ)|=(3430929381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054672607/2500000000 : ℝ)|^67 ≤ (16090010917389/50000000000000 : ℝ)^51
        have hw : |(1054672607/2500000000 : ℝ)|=(1054672607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4074889327/10000000000 : ℝ)*x 0 + (-1988842341/5000000000 : ℝ)*x 1 + (-76996511/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4074889327/10000000000 : ℝ)^67 ≤ (15373374827023/50000000000000 : ℝ)^51 := by
    have hnat : (4074889327 : ℕ)^67*50000000000000^51 ≤ 15373374827023^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074889327 10000000000 15373374827023 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988842341/5000000000 : ℝ)^67 ≤ (14893411648139/50000000000000 : ℝ)^51 := by
    have hnat : (1988842341 : ℕ)^67*50000000000000^51 ≤ 14893411648139^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988842341 5000000000 14893411648139 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76996511/156250000 : ℝ)^67 ≤ (9866606758289/25000000000000 : ℝ)^51 := by
    have hnat : (76996511 : ℕ)^67*25000000000000^51 ≤ 9866606758289^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76996511 156250000 9866606758289 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4074889327/10000000000 : ℝ), (-1988842341/5000000000 : ℝ), (-76996511/156250000 : ℝ)] ![(15373374827023/50000000000000 : ℝ), (14893411648139/50000000000000 : ℝ), (9866606758289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4074889327/10000000000 : ℝ)|^67 ≤ (15373374827023/50000000000000 : ℝ)^51
        have hw : |(4074889327/10000000000 : ℝ)|=(4074889327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988842341/5000000000 : ℝ)|^67 ≤ (14893411648139/50000000000000 : ℝ)^51
        have hw : |(-1988842341/5000000000 : ℝ)|=(1988842341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76996511/156250000 : ℝ)|^67 ≤ (9866606758289/25000000000000 : ℝ)^51
        have hw : |(-76996511/156250000 : ℝ)|=(76996511/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305085_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2416088293/5000000000 : ℝ)*x 0 + (-17179451/40000000 : ℝ)*x 1 + (1927762071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2416088293/5000000000 : ℝ)^67 ≤ (19231818205909/50000000000000 : ℝ)^51 := by
    have hnat : (2416088293 : ℕ)^67*50000000000000^51 ≤ 19231818205909^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416088293 5000000000 19231818205909 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17179451/40000000 : ℝ)^67 ≤ (3294550172133/10000000000000 : ℝ)^51 := by
    have hnat : (17179451 : ℕ)^67*10000000000000^51 ≤ 3294550172133^51*40000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17179451 40000000 3294550172133 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1927762071/5000000000 : ℝ)^67 ≤ (28590861852427/100000000000000 : ℝ)^51 := by
    have hnat : (1927762071 : ℕ)^67*100000000000000^51 ≤ 28590861852427^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927762071 5000000000 28590861852427 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2416088293/5000000000 : ℝ), (-17179451/40000000 : ℝ), (1927762071/5000000000 : ℝ)] ![(19231818205909/50000000000000 : ℝ), (3294550172133/10000000000000 : ℝ), (28590861852427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2416088293/5000000000 : ℝ)|^67 ≤ (19231818205909/50000000000000 : ℝ)^51
        have hw : |(2416088293/5000000000 : ℝ)|=(2416088293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17179451/40000000 : ℝ)|^67 ≤ (3294550172133/10000000000000 : ℝ)^51
        have hw : |(-17179451/40000000 : ℝ)|=(17179451/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1927762071/5000000000 : ℝ)|^67 ≤ (28590861852427/100000000000000 : ℝ)^51
        have hw : |(1927762071/5000000000 : ℝ)|=(1927762071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305085 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1001234149/5000000000 : ℝ)*X 0 0+(-1872767423/2500000000 : ℝ)*X 0 1+(2880003589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5618152077/10000000000 : ℝ)*X 1 0+(354296501/1250000000 : ℝ)*X 1 1+(4402113133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((675826119/1000000000 : ℝ)*X 0 0+(-229776953/1000000000 : ℝ)*X 0 1+(445026807/1250000000 : ℝ)*X 0 2+(675826119/1000000000 : ℝ)*X 1 0+(-229776953/1000000000 : ℝ)*X 1 1+(445026807/1250000000 : ℝ)*X 1 2+(675826119/1000000000 : ℝ)*X 2 0+(-229776953/1000000000 : ℝ)*X 2 1+(445026807/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-46642293/312500000 : ℝ)*X 0 0+(-2082074089/2500000000 : ℝ)*X 0 1+(266739811/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((564579453/1000000000 : ℝ)*X 1 0+(2659133649/10000000000 : ℝ)*X 1 1+(180914501/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4199371589/10000000000 : ℝ)*X 2 0+(-1289295007/5000000000 : ℝ)*X 2 1+(-1200776711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_11 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_11 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-941007017/5000000000 : ℝ)*X 0 0+(-3787303463/5000000000 : ℝ)*X 0 1+(2873499387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2323726547/5000000000 : ℝ)*X 1 0+(1469524781/5000000000 : ℝ)*X 1 1+(132528473/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4198636431/10000000000 : ℝ)*X 2 0+(-2879948211/10000000000 : ℝ)*X 2 1+(-5767771723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2125288369/2500000000 : ℝ)*X 0 0+(-183633349/1250000000 : ℝ)*X 0 1+(376862203/2000000000 : ℝ)*X 0 2+(2125288369/2500000000 : ℝ)*X 1 0+(-183633349/1250000000 : ℝ)*X 1 1+(376862203/2000000000 : ℝ)*X 1 2+(2125288369/2500000000 : ℝ)*X 2 0+(-183633349/1250000000 : ℝ)*X 2 1+(376862203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1232240247/10000000000 : ℝ)*X 0 0+(-8303556697/10000000000 : ℝ)*X 0 1+(29913443/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((402076997/625000000 : ℝ)*X 1 0+(63194411/250000000 : ℝ)*X 1 1+(3749481117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3448696403/10000000000 : ℝ)*X 2 0+(-168808093/500000000 : ℝ)*X 2 1+(-150390943/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2102565443/2500000000 : ℝ)*X 0 0+(-681226733/10000000000 : ℝ)*X 0 1+(33039167/125000000 : ℝ)*X 0 2+(2102565443/2500000000 : ℝ)*X 1 0+(-681226733/10000000000 : ℝ)*X 1 1+(33039167/125000000 : ℝ)*X 1 2+(2102565443/2500000000 : ℝ)*X 2 0+(-681226733/10000000000 : ℝ)*X 2 1+(33039167/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1283/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1283/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17796567676613619451893/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513036796537/200000000000 : ℝ)*(base3) + (424648922031/500000000000 : ℝ)*(base40) + (504672200661/250000000000 : ℝ)*(base50) + (3922911937501/1000000000000 : ℝ)*(major_s0_0) + (4283406740467/1000000000000 : ℝ)*(major_s0_1) + (3922911937501/1000000000000 : ℝ)*(major_s0_2) + (559423/31250000000 : ℝ)*(sp_s0_6) + (5280565391261/1000000000000 : ℝ)*(sp_s0_7) + (1961430171219/250000000000 : ℝ)*(sp_s0_8) + (1320138622651/250000000000 : ℝ)*(sp_s0_9) + (360494802967/1000000000000 : ℝ)*(sp_s0_11) + (80542831/1000000000000 : ℝ)*(sp_s0_15) + (51853761/1000000000000 : ℝ)*(sp_s0_21) + (31377209/500000000000 : ℝ)*(sp_s0_23) + (128260094211/50000000000 : ℝ)*(f.failure) + (2640308622511/500000000000 : ℝ)*(f.sum) + (565516159756359/10000000000000000000000000000 : ℝ)*base63 + (7642501975816397/10000000000000000000000000000 : ℝ)*base65 + (3211439980228757/5000000000000000000000000000 : ℝ)*base67 + (84940240990629/5000000000000000000000000000 : ℝ)*base69 + (135789437440469/2000000000000000000000000000 : ℝ)*base70 + (3047669601183603/10000000000000000000000000000 : ℝ)*base73 + (3437476130775101/10000000000000000000000000000 : ℝ)*base75 + (3477694865990629/5000000000000000000000000000 : ℝ)*base77 + (5355435785641117/10000000000000000000000000000 : ℝ)*base79 + (649/625000000000000 : ℝ)*base86 + (3/78125000000000 : ℝ)*base88 + (649/625000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-131/800 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-131/800 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30548877977215484010513/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460732194053/500000000000 : ℝ)*(base40) + (1550367/1000000000000 : ℝ)*(base50) + (3656764627/25000000000 : ℝ)*(base59) + (3241504840767/1000000000000 : ℝ)*(major_s0_0) + (3241504840767/1000000000000 : ℝ)*(major_s0_1) + (3241504840767/1000000000000 : ℝ)*(major_s0_2) + (1457959/5000000000 : ℝ)*(sp_s0_0) + (27445437/1000000000000 : ℝ)*(sp_s0_7) + (11262219/500000000000 : ℝ)*(sp_s0_8) + (405214179/1000000000000 : ℝ)*(sp_s0_9) + (4363058484187/1000000000000 : ℝ)*(sp_s0_14) + (872670999397/200000000000 : ℝ)*(sp_s0_15) + (1090743076811/250000000000 : ℝ)*(sp_s0_16) + (2119628086921/1000000000000 : ℝ)*(sp_s0_20) + (2119628086921/1000000000000 : ℝ)*(f.failure) + (4363377521423/1000000000000 : ℝ)*(f.sum) + (1261850752625887/10000000000000000000000000000 : ℝ)*base63 + (753012344593999/10000000000000000000000000000 : ℝ)*base65 + (271073148609943/5000000000000000000000000000 : ℝ)*base66 + (3321137765609943/5000000000000000000000000000 : ℝ)*base69 + (1133140767162777/2000000000000000000000000000 : ℝ)*base71 + (850170456406001/10000000000000000000000000000 : ℝ)*base73 + (4435493430406001/10000000000000000000000000000 : ℝ)*base75 + (506792539609943/5000000000000000000000000000 : ℝ)*base77 + (1775361658762777/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (177/390625000000000 : ℝ)*base86 + (177/390625000000000 : ℝ)*base88 + (177/390625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43733/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11867105706322466856717/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247111065999/200000000000 : ℝ)*(base3) + (1779920692607/1000000000000 : ℝ)*(base40) + (1606460654469/1000000000000 : ℝ)*(base50) + (33644797633/250000000000 : ℝ)*(base59) + (2653718549313/500000000000 : ℝ)*(major_s0_0) + (2653718549313/500000000000 : ℝ)*(major_s0_1) + (2653718549313/500000000000 : ℝ)*(major_s0_2) + (581581/250000000000 : ℝ)*(sp_s0_1) + (20895173/250000000000 : ℝ)*(sp_s0_7) + (20350359/1000000000000 : ℝ)*(sp_s0_20) + (3572121349823/500000000000 : ℝ)*(sp_s0_21) + (8379879284009/1000000000000 : ℝ)*(sp_s0_22) + (3572163140169/500000000000 : ℝ)*(sp_s0_23) + (1117485327139/500000000000 : ℝ)*(sp_s0_27) + (433818291829/125000000000 : ℝ)*(f.failure) + (3572163140169/500000000000 : ℝ)*(f.sum) + (43875279647007/5000000000000000000000000000 : ℝ)*base62 + (30973470547761/5000000000000000000000000000 : ℝ)*base65 + (116486796799623/2500000000000000000000000000 : ℝ)*base67 + (457129348950377/2500000000000000000000000000 : ℝ)*base69 + (356217918689703/1000000000000000000000000000 : ℝ)*base71 + (627021582452239/5000000000000000000000000000 : ℝ)*base73 + (735225030452239/5000000000000000000000000000 : ℝ)*base75 + (306298201549623/2500000000000000000000000000 : ℝ)*base76 + (218594274189703/1000000000000000000000000000 : ℝ)*base78 + (39/1562500000000000 : ℝ)*base87 + (39/1562500000000000 : ℝ)*base89 + (39/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1283/6250 : ℝ) ^ (133/32 : ℝ) ≤ (2773133097124633/2000000000000000000 : ℝ) := by
    have hpowers : (1283/6250 : ℝ)^133 ≤ (2773133097124633/2000000000000000000 : ℝ)^32 := by
      have hnat : (1283 : ℕ)^133*2000000000000000000^32 ≤ 2773133097124633^32*6250^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1283 6250 2773133097124633 2000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1283/6250 : ℝ)) (X := (2773133097124633/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2002773133097124633/2000000000000000000 : ℝ) ≤ (10003334345009189/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2002773133097124633/2000000000000000000 : ℝ)^32 ≤ (10003334345009189/10000000000000000 : ℝ)^133 := by
      have hnat : (2002773133097124633 : ℕ)^32*10000000000000000^133 ≤ 10003334345009189^133*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002773133097124633 2000000000000000000 10003334345009189 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003334345009189/10000000000000000 : ℝ)) (X := (2002773133097124633/2000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1002773133097124633/1000000000000000000 : ℝ) ≤ (10006665185800457/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1002773133097124633/1000000000000000000 : ℝ)^32 ≤ (10006665185800457/10000000000000000 : ℝ)^133 := by
      have hnat : (1002773133097124633 : ℕ)^32*10000000000000000^133 ≤ 10006665185800457^133*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002773133097124633 1000000000000000000 10006665185800457 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006665185800457/10000000000000000 : ℝ)) (X := (1002773133097124633/1000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3334345009189/2052800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(832710197817/513200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1283/6250 : ℝ)) (alpha := (3334345009189/2052800000000000 : ℝ)) (beta := (832710197817/513200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1283/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3334345009189/2052800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(832710197817/513200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (131/800 : ℝ) ^ (133/32 : ℝ) ≤ (54192734324446369/100000000000000000000 : ℝ) := by
    have hpowers : (131/800 : ℝ)^133 ≤ (54192734324446369/100000000000000000000 : ℝ)^32 := by
      have hnat : (131 : ℕ)^133*100000000000000000000^32 ≤ 54192734324446369^32*800^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 800 54192734324446369 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/800 : ℝ)) (X := (54192734324446369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100054192734324446369/100000000000000000000 : ℝ) ≤ (500065180856133/500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100054192734324446369/100000000000000000000 : ℝ)^32 ≤ (500065180856133/500000000000000 : ℝ)^133 := by
      have hnat : (100054192734324446369 : ℕ)^32*500000000000000^133 ≤ 500065180856133^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054192734324446369 100000000000000000000 500065180856133 500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500065180856133/500000000000000 : ℝ)) (X := (100054192734324446369/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50054192734324446369/50000000000000000000 : ℝ) ≤ (2500651674539271/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50054192734324446369/50000000000000000000 : ℝ)^32 ≤ (2500651674539271/2500000000000000 : ℝ)^133 := by
      have hnat : (50054192734324446369 : ℕ)^32*2500000000000000^133 ≤ 2500651674539271^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054192734324446369 50000000000000000000 2500651674539271 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500651674539271/2500000000000000 : ℝ)) (X := (50054192734324446369/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(65180856133/81875000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(162885129303/204687500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (131/800 : ℝ)) (alpha := (65180856133/81875000000000 : ℝ)) (beta := (162885129303/204687500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (131/800 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(65180856133/81875000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(162885129303/204687500000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (43733/100000 : ℝ) ^ (133/32 : ℝ) ≤ (1607250366031633857/50000000000000000000 : ℝ) := by
    have hpowers : (43733/100000 : ℝ)^133 ≤ (1607250366031633857/50000000000000000000 : ℝ)^32 := by
      have hnat : (43733 : ℕ)^133*50000000000000000000^32 ≤ 1607250366031633857^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43733 100000 1607250366031633857 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43733/100000 : ℝ)) (X := (1607250366031633857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51607250366031633857/50000000000000000000 : ℝ) ≤ (5038207398275821/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (51607250366031633857/50000000000000000000 : ℝ)^32 ≤ (5038207398275821/5000000000000000 : ℝ)^133 := by
      have hnat : (51607250366031633857 : ℕ)^32*5000000000000000^133 ≤ 5038207398275821^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51607250366031633857 50000000000000000000 5038207398275821 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038207398275821/5000000000000000 : ℝ)) (X := (51607250366031633857/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26607250366031633857/25000000000000000000 : ℝ) ≤ (1015104314575553/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (26607250366031633857/25000000000000000000 : ℝ)^32 ≤ (1015104314575553/1000000000000000 : ℝ)^133 := by
      have hnat : (26607250366031633857 : ℕ)^32*1000000000000000^133 ≤ 1015104314575553^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26607250366031633857 25000000000000000000 1015104314575553 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1015104314575553/1000000000000000 : ℝ)) (X := (26607250366031633857/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(38207398275821/2186650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4664271825243/273331250000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (43733/100000 : ℝ)) (alpha := (38207398275821/2186650000000000 : ℝ)) (beta := (4664271825243/273331250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43733/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(38207398275821/2186650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4664271825243/273331250000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-666129131/2000000000 : ℝ)*X 0 0+(-2774540083/5000000000 : ℝ)*X 0 1+(80555209/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5287337431/10000000000 : ℝ)*X 1 0+(3430929381/10000000000 : ℝ)*X 1 1+(1054672607/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4074889327/10000000000 : ℝ)*X 2 0+(-1988842341/5000000000 : ℝ)*X 2 1+(-76996511/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2416088293/5000000000 : ℝ)*X 0 0+(-17179451/40000000 : ℝ)*X 0 1+(1927762071/5000000000 : ℝ)*X 0 2+(2416088293/5000000000 : ℝ)*X 1 0+(-17179451/40000000 : ℝ)*X 1 1+(1927762071/5000000000 : ℝ)*X 1 2+(2416088293/5000000000 : ℝ)*X 2 0+(-17179451/40000000 : ℝ)*X 2 1+(1927762071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-8948155353640807598774430927770313/1470067301800000000000000000000000 : ℝ) := by norm_num
    linear_combination (8657/1000000000000 : ℝ)*(base21) + (32463/1000000000000 : ℝ)*(base22) + (66779/1000000000000 : ℝ)*(base33) + (17339/1000000000000 : ℝ)*(base39) + (290250533457/1000000000000 : ℝ)*(base40) + (52396572769/500000000000 : ℝ)*(base49) + (16264535367/50000000000 : ℝ)*(base50) + (12137/500000000000 : ℝ)*(base59) + (1529279933221/1000000000000 : ℝ)*(major_s1_0) + (4779/3125 : ℝ)*(major_s1_1) + (4779/3125 : ℝ)*(major_s1_2) + (2028967277591/1000000000000 : ℝ)*(sp_s1_0) + (507241802703/250000000000 : ℝ)*(sp_s1_1) + (2028967169693/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2028967277591/1000000000000 : ℝ)*(f.sum) + (493707374450717/11458046000000000000000000000 : ℝ)*base62 + (73832103257849/218665000000000000000000000 : ℝ)*base65 + (7490575789/26200000000000000000000 : ℝ)*base66 + (24787569801869/109332500000000000000000000 : ℝ)*base68 + (2889469607442752397/89775102400000000000000000000000 : ℝ)*base71 + (298757973231037/513200000000000000000000000 : ℝ)*base73 + (938719450041/1310000000000000000000000 : ℝ)*base74 + (116571802366951/2052800000000000000000000000 : ℝ)*base76 + (3941577765297207/67229200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p005_b037 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c305085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b037 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
