-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:12:05.454481+00:00
-- url     : https://prove2.me/submissions/daf6ee7c-d2bf-4bd4-84c6-b223eea98c79

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312086_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312086 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c312086_s0 p hpa hpb X hX
  have h1 := collision_c312086_s1 p hpa hpb X hX h0
  have h2 := collision_c312086_s2 p hpa hpb X hX h1
  exact collision_c312086_s3 p hpa hpb X hX h2

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
theorem collision_support_c312085_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2791784921/5000000000 : ℝ)*x 0 + (2746542807/10000000000 : ℝ)*x 1 + (4255454013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2791784921/5000000000 : ℝ)^73 ≤ (23704985738223/50000000000000 : ℝ)^57 := by
    have hnat : (2791784921 : ℕ)^73*50000000000000^57 ≤ 23704985738223^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791784921 5000000000 23704985738223 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746542807/10000000000 : ℝ)^73 ≤ (2388706191997/12500000000000 : ℝ)^57 := by
    have hnat : (2746542807 : ℕ)^73*12500000000000^57 ≤ 2388706191997^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746542807 10000000000 2388706191997 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255454013/10000000000 : ℝ)^73 ≤ (8370094743337/25000000000000 : ℝ)^57 := by
    have hnat : (4255454013 : ℕ)^73*25000000000000^57 ≤ 8370094743337^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255454013 10000000000 8370094743337 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2791784921/5000000000 : ℝ), (2746542807/10000000000 : ℝ), (4255454013/10000000000 : ℝ)] ![(23704985738223/50000000000000 : ℝ), (2388706191997/12500000000000 : ℝ), (8370094743337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2791784921/5000000000 : ℝ)|^73 ≤ (23704985738223/50000000000000 : ℝ)^57
        have hw : |(2791784921/5000000000 : ℝ)|=(2791784921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746542807/10000000000 : ℝ)|^73 ≤ (2388706191997/12500000000000 : ℝ)^57
        have hw : |(2746542807/10000000000 : ℝ)|=(2746542807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255454013/10000000000 : ℝ)|^73 ≤ (8370094743337/25000000000000 : ℝ)^57
        have hw : |(4255454013/10000000000 : ℝ)|=(4255454013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (19570219/50000000 : ℝ)*x 0 + (-805705343/2500000000 : ℝ)*x 1 + (-5496688301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19570219/50000000 : ℝ)^73 ≤ (30079803535639/100000000000000 : ℝ)^57 := by
    have hnat : (19570219 : ℕ)^73*100000000000000^57 ≤ 30079803535639^57*50000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19570219 50000000 30079803535639 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805705343/2500000000 : ℝ)^73 ≤ (11726469754431/50000000000000 : ℝ)^57 := by
    have hnat : (805705343 : ℕ)^73*50000000000000^57 ≤ 11726469754431^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805705343 2500000000 11726469754431 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496688301/10000000000 : ℝ)^73 ≤ (23233628471647/50000000000000 : ℝ)^57 := by
    have hnat : (5496688301 : ℕ)^73*50000000000000^57 ≤ 23233628471647^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496688301 10000000000 23233628471647 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19570219/50000000 : ℝ), (-805705343/2500000000 : ℝ), (-5496688301/10000000000 : ℝ)] ![(30079803535639/100000000000000 : ℝ), (11726469754431/50000000000000 : ℝ), (23233628471647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19570219/50000000 : ℝ)|^73 ≤ (30079803535639/100000000000000 : ℝ)^57
        have hw : |(19570219/50000000 : ℝ)|=(19570219/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-805705343/2500000000 : ℝ)|^73 ≤ (11726469754431/50000000000000 : ℝ)^57
        have hw : |(-805705343/2500000000 : ℝ)|=(805705343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5496688301/10000000000 : ℝ)|^73 ≤ (23233628471647/50000000000000 : ℝ)^57
        have hw : |(-5496688301/10000000000 : ℝ)|=(5496688301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6750581667/10000000000 : ℝ)*x 0 + (-2176118693/10000000000 : ℝ)*x 1 + (68516351/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6750581667/10000000000 : ℝ)^73 ≤ (12091132085667/20000000000000 : ℝ)^57 := by
    have hnat : (6750581667 : ℕ)^73*20000000000000^57 ≤ 12091132085667^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6750581667 10000000000 12091132085667 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176118693/10000000000 : ℝ)^73 ≤ (113464212881/800000000000 : ℝ)^57 := by
    have hnat : (2176118693 : ℕ)^73*800000000000^57 ≤ 113464212881^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176118693 10000000000 113464212881 800000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68516351/200000000 : ℝ)^73 ≤ (25361312941819/100000000000000 : ℝ)^57 := by
    have hnat : (68516351 : ℕ)^73*100000000000000^57 ≤ 25361312941819^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68516351 200000000 25361312941819 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6750581667/10000000000 : ℝ), (-2176118693/10000000000 : ℝ), (68516351/200000000 : ℝ)] ![(12091132085667/20000000000000 : ℝ), (113464212881/800000000000 : ℝ), (25361312941819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6750581667/10000000000 : ℝ)|^73 ≤ (12091132085667/20000000000000 : ℝ)^57
        have hw : |(6750581667/10000000000 : ℝ)|=(6750581667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176118693/10000000000 : ℝ)|^73 ≤ (113464212881/800000000000 : ℝ)^57
        have hw : |(-2176118693/10000000000 : ℝ)|=(2176118693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68516351/200000000 : ℝ)|^73 ≤ (25361312941819/100000000000000 : ℝ)^57
        have hw : |(68516351/200000000 : ℝ)|=(68516351/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-409400789/2500000000 : ℝ)*x 0 + (-7910935011/10000000000 : ℝ)*x 1 + (599834077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409400789/2500000000 : ℝ)^73 ≤ (4927262104847/50000000000000 : ℝ)^57 := by
    have hnat : (409400789 : ℕ)^73*50000000000000^57 ≤ 4927262104847^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409400789 2500000000 4927262104847 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7910935011/10000000000 : ℝ)^73 ≤ (74073043013363/100000000000000 : ℝ)^57 := by
    have hnat : (7910935011 : ℕ)^73*100000000000000^57 ≤ 74073043013363^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7910935011 10000000000 74073043013363 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599834077/2500000000 : ℝ)^73 ≤ (3214486552057/20000000000000 : ℝ)^57 := by
    have hnat : (599834077 : ℕ)^73*20000000000000^57 ≤ 3214486552057^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599834077 2500000000 3214486552057 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409400789/2500000000 : ℝ), (-7910935011/10000000000 : ℝ), (599834077/2500000000 : ℝ)] ![(4927262104847/50000000000000 : ℝ), (74073043013363/100000000000000 : ℝ), (3214486552057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409400789/2500000000 : ℝ)|^73 ≤ (4927262104847/50000000000000 : ℝ)^57
        have hw : |(-409400789/2500000000 : ℝ)|=(409400789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7910935011/10000000000 : ℝ)|^73 ≤ (74073043013363/100000000000000 : ℝ)^57
        have hw : |(-7910935011/10000000000 : ℝ)|=(7910935011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599834077/2500000000 : ℝ)|^73 ≤ (3214486552057/20000000000000 : ℝ)^57
        have hw : |(599834077/2500000000 : ℝ)|=(599834077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1135067963/2000000000 : ℝ)*x 0 + (1269925149/5000000000 : ℝ)*x 1 + (542098677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1135067963/2000000000 : ℝ)^73 ≤ (24205104451603/50000000000000 : ℝ)^57 := by
    have hnat : (1135067963 : ℕ)^73*50000000000000^57 ≤ 24205104451603^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135067963 2000000000 24205104451603 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269925149/5000000000 : ℝ)^73 ≤ (17287679977051/100000000000000 : ℝ)^57 := by
    have hnat : (1269925149 : ℕ)^73*100000000000000^57 ≤ 17287679977051^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269925149 5000000000 17287679977051 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542098677/1250000000 : ℝ)^73 ≤ (34302111104767/100000000000000 : ℝ)^57 := by
    have hnat : (542098677 : ℕ)^73*100000000000000^57 ≤ 34302111104767^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542098677 1250000000 34302111104767 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1135067963/2000000000 : ℝ), (1269925149/5000000000 : ℝ), (542098677/1250000000 : ℝ)] ![(24205104451603/50000000000000 : ℝ), (17287679977051/100000000000000 : ℝ), (34302111104767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1135067963/2000000000 : ℝ)|^73 ≤ (24205104451603/50000000000000 : ℝ)^57
        have hw : |(1135067963/2000000000 : ℝ)|=(1135067963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269925149/5000000000 : ℝ)|^73 ≤ (17287679977051/100000000000000 : ℝ)^57
        have hw : |(1269925149/5000000000 : ℝ)|=(1269925149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542098677/1250000000 : ℝ)|^73 ≤ (34302111104767/100000000000000 : ℝ)^57
        have hw : |(542098677/1250000000 : ℝ)|=(542098677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4114775549/10000000000 : ℝ)*x 0 + (-2758377659/10000000000 : ℝ)*x 1 + (-712906169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4114775549/10000000000 : ℝ)^73 ≤ (32069518424239/100000000000000 : ℝ)^57 := by
    have hnat : (4114775549 : ℕ)^73*100000000000000^57 ≤ 32069518424239^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114775549 10000000000 32069518424239 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758377659/10000000000 : ℝ)^73 ≤ (2401896334811/12500000000000 : ℝ)^57 := by
    have hnat : (2758377659 : ℕ)^73*12500000000000^57 ≤ 2401896334811^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758377659 10000000000 2401896334811 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712906169/1250000000 : ℝ)^73 ≤ (48715310877271/100000000000000 : ℝ)^57 := by
    have hnat : (712906169 : ℕ)^73*100000000000000^57 ≤ 48715310877271^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712906169 1250000000 48715310877271 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4114775549/10000000000 : ℝ), (-2758377659/10000000000 : ℝ), (-712906169/1250000000 : ℝ)] ![(32069518424239/100000000000000 : ℝ), (2401896334811/12500000000000 : ℝ), (48715310877271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4114775549/10000000000 : ℝ)|^73 ≤ (32069518424239/100000000000000 : ℝ)^57
        have hw : |(4114775549/10000000000 : ℝ)|=(4114775549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2758377659/10000000000 : ℝ)|^73 ≤ (2401896334811/12500000000000 : ℝ)^57
        have hw : |(-2758377659/10000000000 : ℝ)|=(2758377659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-712906169/1250000000 : ℝ)|^73 ≤ (48715310877271/100000000000000 : ℝ)^57
        have hw : |(-712906169/1250000000 : ℝ)|=(712906169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1974890117/2500000000 : ℝ)*x 0 + (-254992521/2500000000 : ℝ)*x 1 + (730567101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974890117/2500000000 : ℝ)^73 ≤ (36968335280381/50000000000000 : ℝ)^57 := by
    have hnat : (1974890117 : ℕ)^73*50000000000000^57 ≤ 36968335280381^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974890117 2500000000 36968335280381 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254992521/2500000000 : ℝ)^73 ≤ (1074796350323/20000000000000 : ℝ)^57 := by
    have hnat : (254992521 : ℕ)^73*20000000000000^57 ≤ 1074796350323^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254992521 2500000000 1074796350323 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730567101/2500000000 : ℝ)^73 ≤ (2586168459763/12500000000000 : ℝ)^57 := by
    have hnat : (730567101 : ℕ)^73*12500000000000^57 ≤ 2586168459763^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730567101 2500000000 2586168459763 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1974890117/2500000000 : ℝ), (-254992521/2500000000 : ℝ), (730567101/2500000000 : ℝ)] ![(36968335280381/50000000000000 : ℝ), (1074796350323/20000000000000 : ℝ), (2586168459763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1974890117/2500000000 : ℝ)|^73 ≤ (36968335280381/50000000000000 : ℝ)^57
        have hw : |(1974890117/2500000000 : ℝ)|=(1974890117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254992521/2500000000 : ℝ)|^73 ≤ (1074796350323/20000000000000 : ℝ)^57
        have hw : |(-254992521/2500000000 : ℝ)|=(254992521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(730567101/2500000000 : ℝ)|^73 ≤ (2586168459763/12500000000000 : ℝ)^57
        have hw : |(730567101/2500000000 : ℝ)|=(730567101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-977987307/5000000000 : ℝ)*x 0 + (-28526651/39062500 : ℝ)*x 1 + (586162637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977987307/5000000000 : ℝ)^73 ≤ (494888789641/4000000000000 : ℝ)^57 := by
    have hnat : (977987307 : ℕ)^73*4000000000000^57 ≤ 494888789641^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977987307 5000000000 494888789641 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28526651/39062500 : ℝ)^73 ≤ (66860923279369/100000000000000 : ℝ)^57 := by
    have hnat : (28526651 : ℕ)^73*100000000000000^57 ≤ 66860923279369^57*39062500^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28526651 39062500 66860923279369 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586162637/2000000000 : ℝ)^73 ≤ (20766856958471/100000000000000 : ℝ)^57 := by
    have hnat : (586162637 : ℕ)^73*100000000000000^57 ≤ 20766856958471^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586162637 2000000000 20766856958471 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977987307/5000000000 : ℝ), (-28526651/39062500 : ℝ), (586162637/2000000000 : ℝ)] ![(494888789641/4000000000000 : ℝ), (66860923279369/100000000000000 : ℝ), (20766856958471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977987307/5000000000 : ℝ)|^73 ≤ (494888789641/4000000000000 : ℝ)^57
        have hw : |(-977987307/5000000000 : ℝ)|=(977987307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28526651/39062500 : ℝ)|^73 ≤ (66860923279369/100000000000000 : ℝ)^57
        have hw : |(-28526651/39062500 : ℝ)|=(28526651/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(586162637/2000000000 : ℝ)|^73 ≤ (20766856958471/100000000000000 : ℝ)^57
        have hw : |(586162637/2000000000 : ℝ)|=(586162637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4898755233/10000000000 : ℝ)*x 0 + (1486127849/5000000000 : ℝ)*x 1 + (1192754183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4898755233/10000000000 : ℝ)^73 ≤ (8019037782477/20000000000000 : ℝ)^57 := by
    have hnat : (4898755233 : ℕ)^73*20000000000000^57 ≤ 8019037782477^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898755233 10000000000 8019037782477 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486127849/5000000000 : ℝ)^73 ≤ (422873555213/2000000000000 : ℝ)^57 := by
    have hnat : (1486127849 : ℕ)^73*2000000000000^57 ≤ 422873555213^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486127849 5000000000 422873555213 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192754183/2500000000 : ℝ)^73 ≤ (38761133305641/100000000000000 : ℝ)^57 := by
    have hnat : (1192754183 : ℕ)^73*100000000000000^57 ≤ 38761133305641^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192754183 2500000000 38761133305641 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4898755233/10000000000 : ℝ), (1486127849/5000000000 : ℝ), (1192754183/2500000000 : ℝ)] ![(8019037782477/20000000000000 : ℝ), (422873555213/2000000000000 : ℝ), (38761133305641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4898755233/10000000000 : ℝ)|^73 ≤ (8019037782477/20000000000000 : ℝ)^57
        have hw : |(4898755233/10000000000 : ℝ)|=(4898755233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1486127849/5000000000 : ℝ)|^73 ≤ (422873555213/2000000000000 : ℝ)^57
        have hw : |(1486127849/5000000000 : ℝ)|=(1486127849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192754183/2500000000 : ℝ)|^73 ≤ (38761133305641/100000000000000 : ℝ)^57
        have hw : |(1192754183/2500000000 : ℝ)|=(1192754183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (249601661/625000000 : ℝ)*x 0 + (-1556680929/5000000000 : ℝ)*x 1 + (-5517896711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249601661/625000000 : ℝ)^73 ≤ (3858163353957/12500000000000 : ℝ)^57 := by
    have hnat : (249601661 : ℕ)^73*12500000000000^57 ≤ 3858163353957^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249601661 625000000 3858163353957 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1556680929/5000000000 : ℝ)^73 ≤ (2804712004589/12500000000000 : ℝ)^57 := by
    have hnat : (1556680929 : ℕ)^73*12500000000000^57 ≤ 2804712004589^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556680929 5000000000 2804712004589 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517896711/10000000000 : ℝ)^73 ≤ (46696997116011/100000000000000 : ℝ)^57 := by
    have hnat : (5517896711 : ℕ)^73*100000000000000^57 ≤ 46696997116011^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517896711 10000000000 46696997116011 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249601661/625000000 : ℝ), (-1556680929/5000000000 : ℝ), (-5517896711/10000000000 : ℝ)] ![(3858163353957/12500000000000 : ℝ), (2804712004589/12500000000000 : ℝ), (46696997116011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249601661/625000000 : ℝ)|^73 ≤ (3858163353957/12500000000000 : ℝ)^57
        have hw : |(249601661/625000000 : ℝ)|=(249601661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1556680929/5000000000 : ℝ)|^73 ≤ (2804712004589/12500000000000 : ℝ)^57
        have hw : |(-1556680929/5000000000 : ℝ)|=(1556680929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5517896711/10000000000 : ℝ)|^73 ≤ (46696997116011/100000000000000 : ℝ)^57
        have hw : |(-5517896711/10000000000 : ℝ)|=(5517896711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (80163287/100000000 : ℝ)*x 0 + (-693557949/5000000000 : ℝ)*x 1 + (2471441429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80163287/100000000 : ℝ)^73 ≤ (75339247079653/100000000000000 : ℝ)^57 := by
    have hnat : (80163287 : ℕ)^73*100000000000000^57 ≤ 75339247079653^57*100000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80163287 100000000 75339247079653 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693557949/5000000000 : ℝ)^73 ≤ (7967137142217/100000000000000 : ℝ)^57 := by
    have hnat : (693557949 : ℕ)^73*100000000000000^57 ≤ 7967137142217^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693557949 5000000000 7967137142217 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2471441429/10000000000 : ℝ)^73 ≤ (16693615760241/100000000000000 : ℝ)^57 := by
    have hnat : (2471441429 : ℕ)^73*100000000000000^57 ≤ 16693615760241^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471441429 10000000000 16693615760241 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80163287/100000000 : ℝ), (-693557949/5000000000 : ℝ), (2471441429/10000000000 : ℝ)] ![(75339247079653/100000000000000 : ℝ), (7967137142217/100000000000000 : ℝ), (16693615760241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80163287/100000000 : ℝ)|^73 ≤ (75339247079653/100000000000000 : ℝ)^57
        have hw : |(80163287/100000000 : ℝ)|=(80163287/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693557949/5000000000 : ℝ)|^73 ≤ (7967137142217/100000000000000 : ℝ)^57
        have hw : |(-693557949/5000000000 : ℝ)|=(693557949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2471441429/10000000000 : ℝ)|^73 ≤ (16693615760241/100000000000000 : ℝ)^57
        have hw : |(2471441429/10000000000 : ℝ)|=(2471441429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-64196829/400000000 : ℝ)*x 0 + (-7666568999/10000000000 : ℝ)*x 1 + (110451627/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64196829/400000000 : ℝ)^73 ≤ (2400838912353/25000000000000 : ℝ)^57 := by
    have hnat : (64196829 : ℕ)^73*25000000000000^57 ≤ 2400838912353^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64196829 400000000 2400838912353 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7666568999/10000000000 : ℝ)^73 ≤ (4447217581121/6250000000000 : ℝ)^57 := by
    have hnat : (7666568999 : ℕ)^73*6250000000000^57 ≤ 4447217581121^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7666568999 10000000000 4447217581121 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110451627/400000000 : ℝ)^73 ≤ (19241163040313/100000000000000 : ℝ)^57 := by
    have hnat : (110451627 : ℕ)^73*100000000000000^57 ≤ 19241163040313^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110451627 400000000 19241163040313 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64196829/400000000 : ℝ), (-7666568999/10000000000 : ℝ), (110451627/400000000 : ℝ)] ![(2400838912353/25000000000000 : ℝ), (4447217581121/6250000000000 : ℝ), (19241163040313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64196829/400000000 : ℝ)|^73 ≤ (2400838912353/25000000000000 : ℝ)^57
        have hw : |(-64196829/400000000 : ℝ)|=(64196829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7666568999/10000000000 : ℝ)|^73 ≤ (4447217581121/6250000000000 : ℝ)^57
        have hw : |(-7666568999/10000000000 : ℝ)|=(7666568999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110451627/400000000 : ℝ)|^73 ≤ (19241163040313/100000000000000 : ℝ)^57
        have hw : |(110451627/400000000 : ℝ)|=(110451627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5986315831/10000000000 : ℝ)*x 0 + (2604436591/10000000000 : ℝ)*x 1 + (1968915349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5986315831/10000000000 : ℝ)^73 ≤ (51833190518077/100000000000000 : ℝ)^57 := by
    have hnat : (5986315831 : ℕ)^73*100000000000000^57 ≤ 51833190518077^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986315831 10000000000 51833190518077 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604436591/10000000000 : ℝ)^73 ≤ (3570537669801/20000000000000 : ℝ)^57 := by
    have hnat : (2604436591 : ℕ)^73*20000000000000^57 ≤ 3570537669801^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604436591 10000000000 3570537669801 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968915349/5000000000 : ℝ)^73 ≤ (15157060556267/50000000000000 : ℝ)^57 := by
    have hnat : (1968915349 : ℕ)^73*50000000000000^57 ≤ 15157060556267^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968915349 5000000000 15157060556267 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5986315831/10000000000 : ℝ), (2604436591/10000000000 : ℝ), (1968915349/5000000000 : ℝ)] ![(51833190518077/100000000000000 : ℝ), (3570537669801/20000000000000 : ℝ), (15157060556267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5986315831/10000000000 : ℝ)|^73 ≤ (51833190518077/100000000000000 : ℝ)^57
        have hw : |(5986315831/10000000000 : ℝ)|=(5986315831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604436591/10000000000 : ℝ)|^73 ≤ (3570537669801/20000000000000 : ℝ)^57
        have hw : |(2604436591/10000000000 : ℝ)|=(2604436591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1968915349/5000000000 : ℝ)|^73 ≤ (15157060556267/50000000000000 : ℝ)^57
        have hw : |(1968915349/5000000000 : ℝ)|=(1968915349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (893957559/2500000000 : ℝ)*x 0 + (-830086747/2500000000 : ℝ)*x 1 + (-5714833031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893957559/2500000000 : ℝ)^73 ≤ (26792238614803/100000000000000 : ℝ)^57 := by
    have hnat : (893957559 : ℕ)^73*100000000000000^57 ≤ 26792238614803^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893957559 2500000000 26792238614803 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830086747/2500000000 : ℝ)^73 ≤ (24365696581557/100000000000000 : ℝ)^57 := by
    have hnat : (830086747 : ℕ)^73*100000000000000^57 ≤ 24365696581557^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830086747 2500000000 24365696581557 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5714833031/10000000000 : ℝ)^73 ≤ (9768412957169/20000000000000 : ℝ)^57 := by
    have hnat : (5714833031 : ℕ)^73*20000000000000^57 ≤ 9768412957169^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714833031 10000000000 9768412957169 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893957559/2500000000 : ℝ), (-830086747/2500000000 : ℝ), (-5714833031/10000000000 : ℝ)] ![(26792238614803/100000000000000 : ℝ), (24365696581557/100000000000000 : ℝ), (9768412957169/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893957559/2500000000 : ℝ)|^73 ≤ (26792238614803/100000000000000 : ℝ)^57
        have hw : |(893957559/2500000000 : ℝ)|=(893957559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-830086747/2500000000 : ℝ)|^73 ≤ (24365696581557/100000000000000 : ℝ)^57
        have hw : |(-830086747/2500000000 : ℝ)|=(830086747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5714833031/10000000000 : ℝ)|^73 ≤ (9768412957169/20000000000000 : ℝ)^57
        have hw : |(-5714833031/10000000000 : ℝ)|=(5714833031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s0_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8074146089/10000000000 : ℝ)*x 0 + (-195242603/2000000000 : ℝ)*x 1 + (2721144183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8074146089/10000000000 : ℝ)^73 ≤ (38017929485989/50000000000000 : ℝ)^57 := by
    have hnat : (8074146089 : ℕ)^73*50000000000000^57 ≤ 38017929485989^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8074146089 10000000000 38017929485989 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195242603/2000000000 : ℝ)^73 ≤ (5080517926211/100000000000000 : ℝ)^57 := by
    have hnat : (195242603 : ℕ)^73*100000000000000^57 ≤ 5080517926211^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195242603 2000000000 5080517926211 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721144183/10000000000 : ℝ)^73 ≤ (9441811545841/50000000000000 : ℝ)^57 := by
    have hnat : (2721144183 : ℕ)^73*50000000000000^57 ≤ 9441811545841^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721144183 10000000000 9441811545841 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8074146089/10000000000 : ℝ), (-195242603/2000000000 : ℝ), (2721144183/10000000000 : ℝ)] ![(38017929485989/50000000000000 : ℝ), (5080517926211/100000000000000 : ℝ), (9441811545841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8074146089/10000000000 : ℝ)|^73 ≤ (38017929485989/50000000000000 : ℝ)^57
        have hw : |(8074146089/10000000000 : ℝ)|=(8074146089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195242603/2000000000 : ℝ)|^73 ≤ (5080517926211/100000000000000 : ℝ)^57
        have hw : |(-195242603/2000000000 : ℝ)|=(195242603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721144183/10000000000 : ℝ)|^73 ≤ (9441811545841/50000000000000 : ℝ)^57
        have hw : |(2721144183/10000000000 : ℝ)|=(2721144183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-202849621/625000000 : ℝ)*x 0 + (-544997917/1000000000 : ℝ)*x 1 + (3943746257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202849621/625000000 : ℝ)^73 ≤ (4733077315617/20000000000000 : ℝ)^57 := by
    have hnat : (202849621 : ℕ)^73*20000000000000^57 ≤ 4733077315617^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202849621 625000000 4733077315617 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544997917/1000000000 : ℝ)^73 ≤ (45962158088983/100000000000000 : ℝ)^57 := by
    have hnat : (544997917 : ℕ)^73*100000000000000^57 ≤ 45962158088983^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544997917 1000000000 45962158088983 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3943746257/10000000000 : ℝ)^73 ≤ (30372455314381/100000000000000 : ℝ)^57 := by
    have hnat : (3943746257 : ℕ)^73*100000000000000^57 ≤ 30372455314381^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3943746257 10000000000 30372455314381 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202849621/625000000 : ℝ), (-544997917/1000000000 : ℝ), (3943746257/10000000000 : ℝ)] ![(4733077315617/20000000000000 : ℝ), (45962158088983/100000000000000 : ℝ), (30372455314381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202849621/625000000 : ℝ)|^73 ≤ (4733077315617/20000000000000 : ℝ)^57
        have hw : |(-202849621/625000000 : ℝ)|=(202849621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544997917/1000000000 : ℝ)|^73 ≤ (45962158088983/100000000000000 : ℝ)^57
        have hw : |(-544997917/1000000000 : ℝ)|=(544997917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3943746257/10000000000 : ℝ)|^73 ≤ (30372455314381/100000000000000 : ℝ)^57
        have hw : |(3943746257/10000000000 : ℝ)|=(3943746257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1305737817/2500000000 : ℝ)*x 0 + (1665324149/5000000000 : ℝ)*x 1 + (821819967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305737817/2500000000 : ℝ)^73 ≤ (1360142823361/3125000000000 : ℝ)^57 := by
    have hnat : (1305737817 : ℕ)^73*3125000000000^57 ≤ 1360142823361^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305737817 2500000000 1360142823361 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665324149/5000000000 : ℝ)^73 ≤ (12231276092059/50000000000000 : ℝ)^57 := by
    have hnat : (1665324149 : ℕ)^73*50000000000000^57 ≤ 12231276092059^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665324149 5000000000 12231276092059 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821819967/2000000000 : ℝ)^73 ≤ (16006438727057/50000000000000 : ℝ)^57 := by
    have hnat : (821819967 : ℕ)^73*50000000000000^57 ≤ 16006438727057^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821819967 2000000000 16006438727057 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305737817/2500000000 : ℝ), (1665324149/5000000000 : ℝ), (821819967/2000000000 : ℝ)] ![(1360142823361/3125000000000 : ℝ), (12231276092059/50000000000000 : ℝ), (16006438727057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305737817/2500000000 : ℝ)|^73 ≤ (1360142823361/3125000000000 : ℝ)^57
        have hw : |(1305737817/2500000000 : ℝ)|=(1305737817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1665324149/5000000000 : ℝ)|^73 ≤ (12231276092059/50000000000000 : ℝ)^57
        have hw : |(1665324149/5000000000 : ℝ)|=(1665324149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(821819967/2000000000 : ℝ)|^73 ≤ (16006438727057/50000000000000 : ℝ)^57
        have hw : |(821819967/2000000000 : ℝ)|=(821819967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3978029519/10000000000 : ℝ)*x 0 + (-3893127321/10000000000 : ℝ)*x 1 + (-4833734391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3978029519/10000000000 : ℝ)^73 ≤ (153555052739/500000000000 : ℝ)^57 := by
    have hnat : (3978029519 : ℕ)^73*500000000000^57 ≤ 153555052739^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978029519 10000000000 153555052739 500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3893127321/10000000000 : ℝ)^73 ≤ (29874091537283/100000000000000 : ℝ)^57 := by
    have hnat : (3893127321 : ℕ)^73*100000000000000^57 ≤ 29874091537283^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893127321 10000000000 29874091537283 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833734391/10000000000 : ℝ)^73 ≤ (9853724474217/25000000000000 : ℝ)^57 := by
    have hnat : (4833734391 : ℕ)^73*25000000000000^57 ≤ 9853724474217^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833734391 10000000000 9853724474217 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3978029519/10000000000 : ℝ), (-3893127321/10000000000 : ℝ), (-4833734391/10000000000 : ℝ)] ![(153555052739/500000000000 : ℝ), (29874091537283/100000000000000 : ℝ), (9853724474217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3978029519/10000000000 : ℝ)|^73 ≤ (153555052739/500000000000 : ℝ)^57
        have hw : |(3978029519/10000000000 : ℝ)|=(3978029519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3893127321/10000000000 : ℝ)|^73 ≤ (29874091537283/100000000000000 : ℝ)^57
        have hw : |(-3893127321/10000000000 : ℝ)|=(3893127321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4833734391/10000000000 : ℝ)|^73 ≤ (9853724474217/25000000000000 : ℝ)^57
        have hw : |(-4833734391/10000000000 : ℝ)|=(4833734391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312085_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2373426307/5000000000 : ℝ)*x 0 + (-2112090511/5000000000 : ℝ)*x 1 + (3734534421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2373426307/5000000000 : ℝ)^73 ≤ (19254944774847/50000000000000 : ℝ)^57 := by
    have hnat : (2373426307 : ℕ)^73*50000000000000^57 ≤ 19254944774847^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373426307 5000000000 19254944774847 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112090511/5000000000 : ℝ)^73 ≤ (33165594776757/100000000000000 : ℝ)^57 := by
    have hnat : (2112090511 : ℕ)^73*100000000000000^57 ≤ 33165594776757^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112090511 5000000000 33165594776757 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734534421/10000000000 : ℝ)^73 ≤ (28324515665657/100000000000000 : ℝ)^57 := by
    have hnat : (3734534421 : ℕ)^73*100000000000000^57 ≤ 28324515665657^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734534421 10000000000 28324515665657 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2373426307/5000000000 : ℝ), (-2112090511/5000000000 : ℝ), (3734534421/10000000000 : ℝ)] ![(19254944774847/50000000000000 : ℝ), (33165594776757/100000000000000 : ℝ), (28324515665657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2373426307/5000000000 : ℝ)|^73 ≤ (19254944774847/50000000000000 : ℝ)^57
        have hw : |(2373426307/5000000000 : ℝ)|=(2373426307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112090511/5000000000 : ℝ)|^73 ≤ (33165594776757/100000000000000 : ℝ)^57
        have hw : |(-2112090511/5000000000 : ℝ)|=(2112090511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734534421/10000000000 : ℝ)|^73 ≤ (28324515665657/100000000000000 : ℝ)^57
        have hw : |(3734534421/10000000000 : ℝ)|=(3734534421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312085 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2791784921/5000000000 : ℝ)*X 1 0+(2746542807/10000000000 : ℝ)*X 1 1+(4255454013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((19570219/50000000 : ℝ)*X 2 0+(-805705343/2500000000 : ℝ)*X 2 1+(-5496688301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6750581667/10000000000 : ℝ)*X 0 0+(-2176118693/10000000000 : ℝ)*X 0 1+(68516351/200000000 : ℝ)*X 0 2+(6750581667/10000000000 : ℝ)*X 1 0+(-2176118693/10000000000 : ℝ)*X 1 1+(68516351/200000000 : ℝ)*X 1 2+(6750581667/10000000000 : ℝ)*X 2 0+(-2176118693/10000000000 : ℝ)*X 2 1+(68516351/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-409400789/2500000000 : ℝ)*X 0 0+(-7910935011/10000000000 : ℝ)*X 0 1+(599834077/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1135067963/2000000000 : ℝ)*X 1 0+(1269925149/5000000000 : ℝ)*X 1 1+(542098677/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4114775549/10000000000 : ℝ)*X 2 0+(-2758377659/10000000000 : ℝ)*X 2 1+(-712906169/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1974890117/2500000000 : ℝ)*X 0 0+(-254992521/2500000000 : ℝ)*X 0 1+(730567101/2500000000 : ℝ)*X 0 2+(1974890117/2500000000 : ℝ)*X 1 0+(-254992521/2500000000 : ℝ)*X 1 1+(730567101/2500000000 : ℝ)*X 1 2+(1974890117/2500000000 : ℝ)*X 2 0+(-254992521/2500000000 : ℝ)*X 2 1+(730567101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-977987307/5000000000 : ℝ)*X 0 0+(-28526651/39062500 : ℝ)*X 0 1+(586162637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4898755233/10000000000 : ℝ)*X 1 0+(1486127849/5000000000 : ℝ)*X 1 1+(1192754183/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((249601661/625000000 : ℝ)*X 2 0+(-1556680929/5000000000 : ℝ)*X 2 1+(-5517896711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((80163287/100000000 : ℝ)*X 0 0+(-693557949/5000000000 : ℝ)*X 0 1+(2471441429/10000000000 : ℝ)*X 0 2+(80163287/100000000 : ℝ)*X 1 0+(-693557949/5000000000 : ℝ)*X 1 1+(2471441429/10000000000 : ℝ)*X 1 2+(80163287/100000000 : ℝ)*X 2 0+(-693557949/5000000000 : ℝ)*X 2 1+(2471441429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-64196829/400000000 : ℝ)*X 0 0+(-7666568999/10000000000 : ℝ)*X 0 1+(110451627/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5986315831/10000000000 : ℝ)*X 1 0+(2604436591/10000000000 : ℝ)*X 1 1+(1968915349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((893957559/2500000000 : ℝ)*X 2 0+(-830086747/2500000000 : ℝ)*X 2 1+(-5714833031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8074146089/10000000000 : ℝ)*X 0 0+(-195242603/2000000000 : ℝ)*X 0 1+(2721144183/10000000000 : ℝ)*X 0 2+(8074146089/10000000000 : ℝ)*X 1 0+(-195242603/2000000000 : ℝ)*X 1 1+(2721144183/10000000000 : ℝ)*X 1 2+(8074146089/10000000000 : ℝ)*X 2 0+(-195242603/2000000000 : ℝ)*X 2 1+(2721144183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((13799/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13799/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15199723928170635071223/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581223005049/200000000000 : ℝ)*(base3) + (611976294407/500000000000 : ℝ)*(base40) + (2458786508271/1000000000000 : ℝ)*(base50) + (2497165569027/500000000000 : ℝ)*(major_s0_0) + (2497165569027/500000000000 : ℝ)*(major_s0_1) + (2497165569027/500000000000 : ℝ)*(major_s0_2) + (3972847/200000000000 : ℝ)*(sp_s0_6) + (3498224687939/500000000000 : ℝ)*(sp_s0_7) + (990258038759/100000000000 : ℝ)*(sp_s0_8) + (6996438071381/1000000000000 : ℝ)*(sp_s0_9) + (86041356861/1000000000000 : ℝ)*(sp_s0_13) + (4660197/250000000000 : ℝ)*(sp_s0_15) + (6925451/200000000000 : ℝ)*(sp_s0_21) + (5741469/125000000000 : ℝ)*(sp_s0_23) + (2992176246341/1000000000000 : ℝ)*(f.failure) + (6996484003133/1000000000000 : ℝ)*(f.sum) + (1356617642231741/5000000000000000000000000000 : ℝ)*base62 + (1763042687237223/5000000000000000000000000000 : ℝ)*base65 + (921654000252741/2500000000000000000000000000 : ℝ)*base66 + (1504260947247259/2500000000000000000000000000 : ℝ)*base68 + (405141251451459/1000000000000000000000000000 : ℝ)*base70 + (682209071237223/5000000000000000000000000000 : ℝ)*base72 + (2532714563237223/5000000000000000000000000000 : ℝ)*base74 + (210380601997259/2500000000000000000000000000 : ℝ)*base76 + (263004317951459/1000000000000000000000000000 : ℝ)*base79 + (115333/100000000000000000 : ℝ)*base87 + (115333/100000000000000000 : ℝ)*base89 + (115333/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-5051/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-5051/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12391745027732689416321/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358744228697/250000000000 : ℝ)*(base40) + (171718035801/500000000000 : ℝ)*(base50) + (41115211091/500000000000 : ℝ)*(base59) + (4888242545771/1000000000000 : ℝ)*(major_s0_0) + (4888242545771/1000000000000 : ℝ)*(major_s0_1) + (4888242545771/1000000000000 : ℝ)*(major_s0_2) + (2053851/1000000000000 : ℝ)*(sp_s0_1) + (255967483/1000000000000 : ℝ)*(sp_s0_9) + (3423931964733/500000000000 : ℝ)*(sp_s0_14) + (1369572375123/200000000000 : ℝ)*(sp_s0_15) + (6847588096279/1000000000000 : ℝ)*(sp_s0_16) + (292859291/100000000 : ℝ)*(sp_s0_20) + (3973141/200000000000 : ℝ)*(sp_s0_23) + (2412149/100000000000 : ℝ)*(sp_s0_27) + (292861703149/100000000000 : ℝ)*(f.failure) + (3423931964733/500000000000 : ℝ)*(f.sum) + (1909918836518507/10000000000000000000000000000 : ℝ)*base63 + (2822653862810479/10000000000000000000000000000 : ℝ)*base65 + (144093509664493/5000000000000000000000000000 : ℝ)*base66 + (391531153835507/5000000000000000000000000000 : ℝ)*base68 + (709672655827893/2000000000000000000000000000 : ℝ)*base71 + (4184526729810479/10000000000000000000000000000 : ℝ)*base72 + (3477892677810479/10000000000000000000000000000 : ℝ)*base74 + (3644901354164493/5000000000000000000000000000 : ℝ)*base77 + (824296722772107/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (963/10000000000000000 : ℝ)*base86 + (963/10000000000000000 : ℝ)*base88 + (963/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16221/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23007390799685671765113/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (534883492937/250000000000 : ℝ)*(base3) + (771397690391/250000000000 : ℝ)*(base40) + (2891039940557/1000000000000 : ℝ)*(base50) + (4030409/1000000000000 : ℝ)*(base59) + (4642253845363/500000000000 : ℝ)*(major_s0_0) + (4642253845363/500000000000 : ℝ)*(major_s0_1) + (4642253845363/500000000000 : ℝ)*(major_s0_2) + (76027807/250000000000 : ℝ)*(sp_s0_2) + (17918299/1000000000000 : ℝ)*(sp_s0_7) + (880461/4000000000 : ℝ)*(sp_s0_20) + (13006508063671/1000000000000 : ℝ)*(sp_s0_21) + (15146059953719/1000000000000 : ℝ)*(sp_s0_22) + (6503110935371/500000000000 : ℝ)*(sp_s0_23) + (3422729177173/1000000000000 : ℝ)*(sp_s0_27) + (5562483264171/1000000000000 : ℝ)*(f.failure) + (13006525981971/1000000000000 : ℝ)*(f.sum) + (28354897912371/5000000000000000000000000000 : ℝ)*base63 + (3460633835839113/5000000000000000000000000000 : ℝ)*base64 + (1053286846213371/2500000000000000000000000000 : ℝ)*base67 + (16057700786629/2500000000000000000000000000 : ℝ)*base69 + (173515647046829/1000000000000000000000000000 : ℝ)*base71 + (606036193160887/5000000000000000000000000000 : ℝ)*base72 + (2487788737839113/5000000000000000000000000000 : ℝ)*base75 + (282675325963371/2500000000000000000000000000 : ℝ)*base76 + (462014158346829/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (25877/100000000000000000 : ℝ)*base86 + (25877/100000000000000000 : ℝ)*base88 + (25877/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (13799/100000 : ℝ) ^ (9/2 : ℝ) ≤ (1683543254194839/12500000000000000000 : ℝ) := by
    have hpowers : (13799/100000 : ℝ)^9 ≤ (1683543254194839/12500000000000000000 : ℝ)^2 := by
      have hnat : (13799 : ℕ)^9*12500000000000000000^2 ≤ 1683543254194839^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13799 100000 1683543254194839 12500000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13799/100000 : ℝ)) (X := (1683543254194839/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12501683543254194839/12500000000000000000 : ℝ) ≤ (2500074820225887/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (12501683543254194839/12500000000000000000 : ℝ)^2 ≤ (2500074820225887/2500000000000000 : ℝ)^9 := by
      have hnat : (12501683543254194839 : ℕ)^2*2500000000000000^9 ≤ 2500074820225887^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501683543254194839 12500000000000000000 2500074820225887 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074820225887/2500000000000000 : ℝ)) (X := (12501683543254194839/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6251683543254194839/6250000000000000000 : ℝ) ≤ (5000299265231073/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (6251683543254194839/6250000000000000000 : ℝ)^2 ≤ (5000299265231073/5000000000000000 : ℝ)^9 := by
      have hnat : (6251683543254194839 : ℕ)^2*5000000000000000^9 ≤ 5000299265231073^9*6250000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251683543254194839 6250000000000000000 5000299265231073 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000299265231073/5000000000000000 : ℝ)) (X := (6251683543254194839/6250000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(74820225887/344975000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(149624779299/689950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (13799/100000 : ℝ)) (alpha := (74820225887/344975000000000 : ℝ)) (beta := (149624779299/689950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13799/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(74820225887/344975000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(149624779299/689950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5051/50000 : ℝ) ^ (9/2 : ℝ) ≤ (3310039213276713/100000000000000000000 : ℝ) := by
    have hpowers : (5051/50000 : ℝ)^9 ≤ (3310039213276713/100000000000000000000 : ℝ)^2 := by
      have hnat : (5051 : ℕ)^9*100000000000000000000^2 ≤ 3310039213276713^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5051 50000 3310039213276713 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5051/50000 : ℝ)) (X := (3310039213276713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100003310039213276713/100000000000000000000 : ℝ) ≤ (2000014711096027/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (100003310039213276713/100000000000000000000 : ℝ)^2 ≤ (2000014711096027/2000000000000000 : ℝ)^9 := by
      have hnat : (100003310039213276713 : ℕ)^2*2000000000000000^9 ≤ 2000014711096027^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003310039213276713 100000000000000000000 2000014711096027 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014711096027/2000000000000000 : ℝ)) (X := (100003310039213276713/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50003310039213276713/50000000000000000000 : ℝ) ≤ (10000147109066689/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50003310039213276713/50000000000000000000 : ℝ)^2 ≤ (10000147109066689/10000000000000000 : ℝ)^9 := by
      have hnat : (50003310039213276713 : ℕ)^2*10000000000000000^9 ≤ 10000147109066689^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003310039213276713 50000000000000000000 10000147109066689 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000147109066689/10000000000000000 : ℝ)) (X := (50003310039213276713/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(14711096027/202040000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(36776793277/505100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (5051/50000 : ℝ)) (alpha := (14711096027/202040000000000 : ℝ)) (beta := (36776793277/505100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (5051/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(14711096027/202040000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(36776793277/505100000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16221/50000 : ℝ) ^ (9/2 : ℝ) ≤ (315467260310334529/50000000000000000000 : ℝ) := by
    have hpowers : (16221/50000 : ℝ)^9 ≤ (315467260310334529/50000000000000000000 : ℝ)^2 := by
      have hnat : (16221 : ℕ)^9*50000000000000000000^2 ≤ 315467260310334529^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16221 50000 315467260310334529 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16221/50000 : ℝ)) (X := (315467260310334529/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50315467260310334529/50000000000000000000 : ℝ) ≤ (10013986493353657/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50315467260310334529/50000000000000000000 : ℝ)^2 ≤ (10013986493353657/10000000000000000 : ℝ)^9 := by
      have hnat : (50315467260310334529 : ℕ)^2*10000000000000000^9 ≤ 10013986493353657^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50315467260310334529 50000000000000000000 10013986493353657 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013986493353657/10000000000000000 : ℝ)) (X := (50315467260310334529/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25315467260310334529/25000000000000000000 : ℝ) ≤ (10027904946972577/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25315467260310334529/25000000000000000000 : ℝ)^2 ≤ (10027904946972577/10000000000000000 : ℝ)^9 := by
      have hnat : (25315467260310334529 : ℕ)^2*10000000000000000^9 ≤ 10027904946972577^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25315467260310334529 25000000000000000000 10027904946972577 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027904946972577/10000000000000000 : ℝ)) (X := (25315467260310334529/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4662164451219/1081400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(115987113491/27035000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (16221/50000 : ℝ)) (alpha := (4662164451219/1081400000000000 : ℝ)) (beta := (115987113491/27035000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16221/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4662164451219/1081400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(115987113491/27035000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-202849621/625000000 : ℝ)*X 0 0+(-544997917/1000000000 : ℝ)*X 0 1+(3943746257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1305737817/2500000000 : ℝ)*X 1 0+(1665324149/5000000000 : ℝ)*X 1 1+(821819967/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3978029519/10000000000 : ℝ)*X 2 0+(-3893127321/10000000000 : ℝ)*X 2 1+(-4833734391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2373426307/5000000000 : ℝ)*X 0 0+(-2112090511/5000000000 : ℝ)*X 0 1+(3734534421/10000000000 : ℝ)*X 0 2+(2373426307/5000000000 : ℝ)*X 1 0+(-2112090511/5000000000 : ℝ)*X 1 1+(3734534421/10000000000 : ℝ)*X 1 2+(2373426307/5000000000 : ℝ)*X 2 0+(-2112090511/5000000000 : ℝ)*X 2 1+(3734534421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-260112533670930491076282065185379463/37686113584300000000000000000000000 : ℝ) := by norm_num
    linear_combination (517/500000000000 : ℝ)*(base5) + (311/200000000000 : ℝ)*(base19) + (97/50000000000 : ℝ)*(base39) + (350660807717/1000000000000 : ℝ)*(base40) + (108876280823/1000000000000 : ℝ)*(base49) + (388220081791/1000000000000 : ℝ)*(base50) + (381/500000000000 : ℝ)*(base60) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (1669130000009/1000000000000 : ℝ)*(major_s1_2) + (2300693004481/1000000000000 : ℝ)*(sp_s1_0) + (1150346501463/500000000000 : ℝ)*(sp_s1_1) + (2300693005507/1000000000000 : ℝ)*(sp_s1_2) + (499999999483/500000000000 : ℝ)*(sp_s1_6) + (287586625559/125000000000 : ℝ)*(f.sum) + (305250266396042599/5462151400000000000000000000000 : ℝ)*base62 + (9069482516029/13517500000000000000000000 : ℝ)*base65 + (14696047716453/50510000000000000000000000 : ℝ)*base66 + (214518970495909/1081400000000000000000000000 : ℝ)*base68 + (27547799645896011/74611193000000000000000000000 : ℝ)*base71 + (4450561145137/17248750000000000000000000 : ℝ)*base73 + (31512818156107/50510000000000000000000000 : ℝ)*base74 + (58539546006201/137990000000000000000000000 : ℝ)*base77 + (180555664843871301/696987490000000000000000000000 : ℝ)*base78 + (9/1000000000000 : ℝ)*base81 + (9/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (9/1000000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p012_b034 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c312085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c312086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
