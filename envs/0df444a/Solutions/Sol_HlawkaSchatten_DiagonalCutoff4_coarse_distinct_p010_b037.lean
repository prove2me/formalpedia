-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b037
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:17:17.262984+00:00
-- url     : https://prove2.me/submissions/fad2b415-01c4-4fe8-9b22-9b696959e25b

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310086_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310086_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310086 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c310086_s0 p hpa hpb X hX
  have h1 := collision_c310086_s1 p hpa hpb X hX h0
  have h2 := collision_c310086_s2 p hpa hpb X hX h1
  exact collision_c310086_s3 p hpa hpb X hX h2

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
theorem collision_support_c310085_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014212001/10000000000 : ℝ)*x 0 + (-367045457/500000000 : ℝ)*x 1 + (2904024207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014212001/10000000000 : ℝ)^71 ≤ (1579694341753/12500000000000 : ℝ)^55 := by
    have hnat : (2014212001 : ℕ)^71*12500000000000^55 ≤ 1579694341753^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014212001 10000000000 1579694341753 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367045457/500000000 : ℝ)^71 ≤ (16773947058187/25000000000000 : ℝ)^55 := by
    have hnat : (367045457 : ℕ)^71*25000000000000^55 ≤ 16773947058187^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367045457 500000000 16773947058187 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2904024207/10000000000 : ℝ)^71 ≤ (10133328511661/50000000000000 : ℝ)^55 := by
    have hnat : (2904024207 : ℕ)^71*50000000000000^55 ≤ 10133328511661^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2904024207 10000000000 10133328511661 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014212001/10000000000 : ℝ), (-367045457/500000000 : ℝ), (2904024207/10000000000 : ℝ)] ![(1579694341753/12500000000000 : ℝ), (16773947058187/25000000000000 : ℝ), (10133328511661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014212001/10000000000 : ℝ)|^71 ≤ (1579694341753/12500000000000 : ℝ)^55
        have hw : |(-2014212001/10000000000 : ℝ)|=(2014212001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-367045457/500000000 : ℝ)|^71 ≤ (16773947058187/25000000000000 : ℝ)^55
        have hw : |(-367045457/500000000 : ℝ)|=(367045457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2904024207/10000000000 : ℝ)|^71 ≤ (10133328511661/50000000000000 : ℝ)^55
        have hw : |(2904024207/10000000000 : ℝ)|=(2904024207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5592715259/10000000000 : ℝ)*x 0 + (2773942679/10000000000 : ℝ)*x 1 + (1075747967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5592715259/10000000000 : ℝ)^71 ≤ (11807117060437/25000000000000 : ℝ)^55 := by
    have hnat : (5592715259 : ℕ)^71*25000000000000^55 ≤ 11807117060437^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592715259 10000000000 11807117060437 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773942679/10000000000 : ℝ)^71 ≤ (238780848137/1250000000000 : ℝ)^55 := by
    have hnat : (2773942679 : ℕ)^71*1250000000000^55 ≤ 238780848137^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773942679 10000000000 238780848137 1250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075747967/2500000000 : ℝ)^71 ≤ (1052158246667/3125000000000 : ℝ)^55 := by
    have hnat : (1075747967 : ℕ)^71*3125000000000^55 ≤ 1052158246667^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075747967 2500000000 1052158246667 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5592715259/10000000000 : ℝ), (2773942679/10000000000 : ℝ), (1075747967/2500000000 : ℝ)] ![(11807117060437/25000000000000 : ℝ), (238780848137/1250000000000 : ℝ), (1052158246667/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5592715259/10000000000 : ℝ)|^71 ≤ (11807117060437/25000000000000 : ℝ)^55
        have hw : |(5592715259/10000000000 : ℝ)|=(5592715259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2773942679/10000000000 : ℝ)|^71 ≤ (238780848137/1250000000000 : ℝ)^55
        have hw : |(2773942679/10000000000 : ℝ)|=(2773942679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075747967/2500000000 : ℝ)|^71 ≤ (1052158246667/3125000000000 : ℝ)^55
        have hw : |(1075747967/2500000000 : ℝ)|=(1075747967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-804440817/5000000000 : ℝ)*x 0 + (-4029806379/5000000000 : ℝ)*x 1 + (22823971/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804440817/5000000000 : ℝ)^71 ≤ (147745671299/1562500000000 : ℝ)^55 := by
    have hnat : (804440817 : ℕ)^71*1562500000000^55 ≤ 147745671299^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804440817 5000000000 147745671299 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029806379/5000000000 : ℝ)^71 ≤ (75693766766863/100000000000000 : ℝ)^55 := by
    have hnat : (4029806379 : ℕ)^71*100000000000000^55 ≤ 75693766766863^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029806379 5000000000 75693766766863 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22823971/100000000 : ℝ)^71 ≤ (7425255128881/50000000000000 : ℝ)^55 := by
    have hnat : (22823971 : ℕ)^71*50000000000000^55 ≤ 7425255128881^55*100000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22823971 100000000 7425255128881 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-804440817/5000000000 : ℝ), (-4029806379/5000000000 : ℝ), (22823971/100000000 : ℝ)] ![(147745671299/1562500000000 : ℝ), (75693766766863/100000000000000 : ℝ), (7425255128881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-804440817/5000000000 : ℝ)|^71 ≤ (147745671299/1562500000000 : ℝ)^55
        have hw : |(-804440817/5000000000 : ℝ)|=(804440817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4029806379/5000000000 : ℝ)|^71 ≤ (75693766766863/100000000000000 : ℝ)^55
        have hw : |(-4029806379/5000000000 : ℝ)|=(4029806379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22823971/100000000 : ℝ)|^71 ≤ (7425255128881/50000000000000 : ℝ)^55
        have hw : |(22823971/100000000 : ℝ)|=(22823971/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2835756629/5000000000 : ℝ)*x 0 + (322032473/1250000000 : ℝ)*x 1 + (4389668667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2835756629/5000000000 : ℝ)^71 ≤ (24044610256979/50000000000000 : ℝ)^55 := by
    have hnat : (2835756629 : ℕ)^71*50000000000000^55 ≤ 24044610256979^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835756629 5000000000 24044610256979 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322032473/1250000000 : ℝ)^71 ≤ (17363656665823/100000000000000 : ℝ)^55 := by
    have hnat : (322032473 : ℕ)^71*100000000000000^55 ≤ 17363656665823^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322032473 1250000000 17363656665823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4389668667/10000000000 : ℝ)^71 ≤ (8636780698537/25000000000000 : ℝ)^55 := by
    have hnat : (4389668667 : ℕ)^71*25000000000000^55 ≤ 8636780698537^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389668667 10000000000 8636780698537 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2835756629/5000000000 : ℝ), (322032473/1250000000 : ℝ), (4389668667/10000000000 : ℝ)] ![(24044610256979/50000000000000 : ℝ), (17363656665823/100000000000000 : ℝ), (8636780698537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2835756629/5000000000 : ℝ)|^71 ≤ (24044610256979/50000000000000 : ℝ)^55
        have hw : |(2835756629/5000000000 : ℝ)|=(2835756629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322032473/1250000000 : ℝ)|^71 ≤ (17363656665823/100000000000000 : ℝ)^55
        have hw : |(322032473/1250000000 : ℝ)|=(322032473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4389668667/10000000000 : ℝ)|^71 ≤ (8636780698537/25000000000000 : ℝ)^55
        have hw : |(4389668667/10000000000 : ℝ)|=(4389668667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2057341003/5000000000 : ℝ)*x 0 + (-1342216883/5000000000 : ℝ)*x 1 + (-1459296023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057341003/5000000000 : ℝ)^71 ≤ (31779217138063/100000000000000 : ℝ)^55 := by
    have hnat : (2057341003 : ℕ)^71*100000000000000^55 ≤ 31779217138063^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057341003 5000000000 31779217138063 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342216883/5000000000 : ℝ)^71 ≤ (9155261497933/50000000000000 : ℝ)^55 := by
    have hnat : (1342216883 : ℕ)^71*50000000000000^55 ≤ 9155261497933^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342216883 5000000000 9155261497933 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459296023/2500000000 : ℝ)^71 ≤ (3119391241029/6250000000000 : ℝ)^55 := by
    have hnat : (1459296023 : ℕ)^71*6250000000000^55 ≤ 3119391241029^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459296023 2500000000 3119391241029 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2057341003/5000000000 : ℝ), (-1342216883/5000000000 : ℝ), (-1459296023/2500000000 : ℝ)] ![(31779217138063/100000000000000 : ℝ), (9155261497933/50000000000000 : ℝ), (3119391241029/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2057341003/5000000000 : ℝ)|^71 ≤ (31779217138063/100000000000000 : ℝ)^55
        have hw : |(2057341003/5000000000 : ℝ)|=(2057341003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342216883/5000000000 : ℝ)|^71 ≤ (9155261497933/50000000000000 : ℝ)^55
        have hw : |(-1342216883/5000000000 : ℝ)|=(1342216883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1459296023/2500000000 : ℝ)|^71 ≤ (3119391241029/6250000000000 : ℝ)^55
        have hw : |(-1459296023/2500000000 : ℝ)|=(1459296023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1519612033/2500000000 : ℝ)*x 0 + (-1631938203/10000000000 : ℝ)*x 1 + (2352315167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1519612033/2500000000 : ℝ)^71 ≤ (6573642223323/12500000000000 : ℝ)^55 := by
    have hnat : (1519612033 : ℕ)^71*12500000000000^55 ≤ 6573642223323^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519612033 2500000000 6573642223323 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1631938203/10000000000 : ℝ)^71 ≤ (1926203007539/20000000000000 : ℝ)^55 := by
    have hnat : (1631938203 : ℕ)^71*20000000000000^55 ≤ 1926203007539^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631938203 10000000000 1926203007539 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2352315167/5000000000 : ℝ)^71 ≤ (1511193886453/4000000000000 : ℝ)^55 := by
    have hnat : (2352315167 : ℕ)^71*4000000000000^55 ≤ 1511193886453^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352315167 5000000000 1511193886453 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1519612033/2500000000 : ℝ), (-1631938203/10000000000 : ℝ), (2352315167/5000000000 : ℝ)] ![(6573642223323/12500000000000 : ℝ), (1926203007539/20000000000000 : ℝ), (1511193886453/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1519612033/2500000000 : ℝ)|^71 ≤ (6573642223323/12500000000000 : ℝ)^55
        have hw : |(1519612033/2500000000 : ℝ)|=(1519612033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1631938203/10000000000 : ℝ)|^71 ≤ (1926203007539/20000000000000 : ℝ)^55
        have hw : |(-1631938203/10000000000 : ℝ)|=(1631938203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2352315167/5000000000 : ℝ)|^71 ≤ (1511193886453/4000000000000 : ℝ)^55
        have hw : |(2352315167/5000000000 : ℝ)|=(2352315167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-76226649/400000000 : ℝ)*x 0 + (-1481487589/2000000000 : ℝ)*x 1 + (2913585313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76226649/400000000 : ℝ)^71 ≤ (11765378862239/100000000000000 : ℝ)^55 := by
    have hnat : (76226649 : ℕ)^71*100000000000000^55 ≤ 11765378862239^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76226649 400000000 11765378862239 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1481487589/2000000000 : ℝ)^71 ≤ (6788178668369/10000000000000 : ℝ)^55 := by
    have hnat : (1481487589 : ℕ)^71*10000000000000^55 ≤ 6788178668369^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481487589 2000000000 6788178668369 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2913585313/10000000000 : ℝ)^71 ≤ (1017641721747/5000000000000 : ℝ)^55 := by
    have hnat : (2913585313 : ℕ)^71*5000000000000^55 ≤ 1017641721747^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913585313 10000000000 1017641721747 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76226649/400000000 : ℝ), (-1481487589/2000000000 : ℝ), (2913585313/10000000000 : ℝ)] ![(11765378862239/100000000000000 : ℝ), (6788178668369/10000000000000 : ℝ), (1017641721747/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76226649/400000000 : ℝ)|^71 ≤ (11765378862239/100000000000000 : ℝ)^55
        have hw : |(-76226649/400000000 : ℝ)|=(76226649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1481487589/2000000000 : ℝ)|^71 ≤ (6788178668369/10000000000000 : ℝ)^55
        have hw : |(-1481487589/2000000000 : ℝ)|=(1481487589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2913585313/10000000000 : ℝ)|^71 ≤ (1017641721747/5000000000000 : ℝ)^55
        have hw : |(2913585313/10000000000 : ℝ)|=(2913585313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2379494251/5000000000 : ℝ)*x 0 + (2938123543/10000000000 : ℝ)*x 1 + (2510039103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2379494251/5000000000 : ℝ)^71 ≤ (9586073306419/25000000000000 : ℝ)^55 := by
    have hnat : (2379494251 : ℕ)^71*25000000000000^55 ≤ 9586073306419^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379494251 5000000000 9586073306419 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2938123543/10000000000 : ℝ)^71 ≤ (1028719092621/5000000000000 : ℝ)^55 := by
    have hnat : (2938123543 : ℕ)^71*5000000000000^55 ≤ 1028719092621^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938123543 10000000000 1028719092621 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510039103/5000000000 : ℝ)^71 ≤ (20540662456899/50000000000000 : ℝ)^55 := by
    have hnat : (2510039103 : ℕ)^71*50000000000000^55 ≤ 20540662456899^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510039103 5000000000 20540662456899 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2379494251/5000000000 : ℝ), (2938123543/10000000000 : ℝ), (2510039103/5000000000 : ℝ)] ![(9586073306419/25000000000000 : ℝ), (1028719092621/5000000000000 : ℝ), (20540662456899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2379494251/5000000000 : ℝ)|^71 ≤ (9586073306419/25000000000000 : ℝ)^55
        have hw : |(2379494251/5000000000 : ℝ)|=(2379494251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2938123543/10000000000 : ℝ)|^71 ≤ (1028719092621/5000000000000 : ℝ)^55
        have hw : |(2938123543/10000000000 : ℝ)|=(2938123543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510039103/5000000000 : ℝ)|^71 ≤ (20540662456899/50000000000000 : ℝ)^55
        have hw : |(2510039103/5000000000 : ℝ)|=(2510039103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2044164063/5000000000 : ℝ)*x 0 + (-46626277/156250000 : ℝ)*x 1 + (-5616922169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044164063/5000000000 : ℝ)^71 ≤ (31516709621973/100000000000000 : ℝ)^55 := by
    have hnat : (2044164063 : ℕ)^71*100000000000000^55 ≤ 31516709621973^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044164063 5000000000 31516709621973 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46626277/156250000 : ℝ)^71 ≤ (10495385132757/50000000000000 : ℝ)^55 := by
    have hnat : (46626277 : ℕ)^71*50000000000000^55 ≤ 10495385132757^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46626277 156250000 10495385132757 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5616922169/10000000000 : ℝ)^71 ≤ (47492520095053/100000000000000 : ℝ)^55 := by
    have hnat : (5616922169 : ℕ)^71*100000000000000^55 ≤ 47492520095053^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616922169 10000000000 47492520095053 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2044164063/5000000000 : ℝ), (-46626277/156250000 : ℝ), (-5616922169/10000000000 : ℝ)] ![(31516709621973/100000000000000 : ℝ), (10495385132757/50000000000000 : ℝ), (47492520095053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2044164063/5000000000 : ℝ)|^71 ≤ (31516709621973/100000000000000 : ℝ)^55
        have hw : |(2044164063/5000000000 : ℝ)|=(2044164063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46626277/156250000 : ℝ)|^71 ≤ (10495385132757/50000000000000 : ℝ)^55
        have hw : |(-46626277/156250000 : ℝ)|=(46626277/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5616922169/10000000000 : ℝ)|^71 ≤ (47492520095053/100000000000000 : ℝ)^55
        have hw : |(-5616922169/10000000000 : ℝ)|=(5616922169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8316436189/10000000000 : ℝ)*x 0 + (-1434929231/10000000000 : ℝ)*x 1 + (2061387471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8316436189/10000000000 : ℝ)^71 ≤ (78821787697979/100000000000000 : ℝ)^55 := by
    have hnat : (8316436189 : ℕ)^71*100000000000000^55 ≤ 78821787697979^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8316436189 10000000000 78821787697979 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1434929231/10000000000 : ℝ)^71 ≤ (8157269390741/100000000000000 : ℝ)^55 := by
    have hnat : (1434929231 : ℕ)^71*100000000000000^55 ≤ 8157269390741^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434929231 10000000000 8157269390741 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061387471/10000000000 : ℝ)^71 ≤ (651047144619/5000000000000 : ℝ)^55 := by
    have hnat : (2061387471 : ℕ)^71*5000000000000^55 ≤ 651047144619^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061387471 10000000000 651047144619 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8316436189/10000000000 : ℝ), (-1434929231/10000000000 : ℝ), (2061387471/10000000000 : ℝ)] ![(78821787697979/100000000000000 : ℝ), (8157269390741/100000000000000 : ℝ), (651047144619/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8316436189/10000000000 : ℝ)|^71 ≤ (78821787697979/100000000000000 : ℝ)^55
        have hw : |(8316436189/10000000000 : ℝ)|=(8316436189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1434929231/10000000000 : ℝ)|^71 ≤ (8157269390741/100000000000000 : ℝ)^55
        have hw : |(-1434929231/10000000000 : ℝ)|=(1434929231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2061387471/10000000000 : ℝ)|^71 ≤ (651047144619/5000000000000 : ℝ)^55
        have hw : |(2061387471/10000000000 : ℝ)|=(2061387471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-696709697/5000000000 : ℝ)*x 0 + (-3994047179/5000000000 : ℝ)*x 1 + (642759969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (696709697/5000000000 : ℝ)^71 ≤ (7853938210609/100000000000000 : ℝ)^55 := by
    have hnat : (696709697 : ℕ)^71*100000000000000^55 ≤ 7853938210609^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696709697 5000000000 7853938210609 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3994047179/5000000000 : ℝ)^71 ≤ (74827807834637/100000000000000 : ℝ)^55 := by
    have hnat : (3994047179 : ℕ)^71*100000000000000^55 ≤ 74827807834637^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3994047179 5000000000 74827807834637 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642759969/2500000000 : ℝ)^71 ≤ (8659126967717/50000000000000 : ℝ)^55 := by
    have hnat : (642759969 : ℕ)^71*50000000000000^55 ≤ 8659126967717^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642759969 2500000000 8659126967717 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-696709697/5000000000 : ℝ), (-3994047179/5000000000 : ℝ), (642759969/2500000000 : ℝ)] ![(7853938210609/100000000000000 : ℝ), (74827807834637/100000000000000 : ℝ), (8659126967717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-696709697/5000000000 : ℝ)|^71 ≤ (7853938210609/100000000000000 : ℝ)^55
        have hw : |(-696709697/5000000000 : ℝ)|=(696709697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3994047179/5000000000 : ℝ)|^71 ≤ (74827807834637/100000000000000 : ℝ)^55
        have hw : |(-3994047179/5000000000 : ℝ)|=(3994047179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642759969/2500000000 : ℝ)|^71 ≤ (8659126967717/50000000000000 : ℝ)^55
        have hw : |(642759969/2500000000 : ℝ)|=(642759969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1559199779/2500000000 : ℝ)*x 0 + (1262907379/5000000000 : ℝ)*x 1 + (3803314251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1559199779/2500000000 : ℝ)^71 ≤ (54364358370311/100000000000000 : ℝ)^55 := by
    have hnat : (1559199779 : ℕ)^71*100000000000000^55 ≤ 54364358370311^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559199779 2500000000 54364358370311 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262907379/5000000000 : ℝ)^71 ≤ (677040502773/4000000000000 : ℝ)^55 := by
    have hnat : (1262907379 : ℕ)^71*4000000000000^55 ≤ 677040502773^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262907379 5000000000 677040502773 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3803314251/10000000000 : ℝ)^71 ≤ (2870962904953/10000000000000 : ℝ)^55 := by
    have hnat : (3803314251 : ℕ)^71*10000000000000^55 ≤ 2870962904953^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3803314251 10000000000 2870962904953 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1559199779/2500000000 : ℝ), (1262907379/5000000000 : ℝ), (3803314251/10000000000 : ℝ)] ![(54364358370311/100000000000000 : ℝ), (677040502773/4000000000000 : ℝ), (2870962904953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1559199779/2500000000 : ℝ)|^71 ≤ (54364358370311/100000000000000 : ℝ)^55
        have hw : |(1559199779/2500000000 : ℝ)|=(1559199779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262907379/5000000000 : ℝ)|^71 ≤ (677040502773/4000000000000 : ℝ)^55
        have hw : |(1262907379/5000000000 : ℝ)|=(1262907379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3803314251/10000000000 : ℝ)|^71 ≤ (2870962904953/10000000000000 : ℝ)^55
        have hw : |(3803314251/10000000000 : ℝ)|=(3803314251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1738625393/5000000000 : ℝ)*x 0 + (-665488469/2000000000 : ℝ)*x 1 + (-2934772497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1738625393/5000000000 : ℝ)^71 ≤ (25572748049023/100000000000000 : ℝ)^55 := by
    have hnat : (1738625393 : ℕ)^71*100000000000000^55 ≤ 25572748049023^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738625393 5000000000 25572748049023 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (665488469/2000000000 : ℝ)^71 ≤ (24159511601521/100000000000000 : ℝ)^55 := by
    have hnat : (665488469 : ℕ)^71*100000000000000^55 ≤ 24159511601521^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665488469 2000000000 24159511601521 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934772497/5000000000 : ℝ)^71 ≤ (12566935083607/25000000000000 : ℝ)^55 := by
    have hnat : (2934772497 : ℕ)^71*25000000000000^55 ≤ 12566935083607^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934772497 5000000000 12566935083607 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1738625393/5000000000 : ℝ), (-665488469/2000000000 : ℝ), (-2934772497/5000000000 : ℝ)] ![(25572748049023/100000000000000 : ℝ), (24159511601521/100000000000000 : ℝ), (12566935083607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1738625393/5000000000 : ℝ)|^71 ≤ (25572748049023/100000000000000 : ℝ)^55
        have hw : |(1738625393/5000000000 : ℝ)|=(1738625393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-665488469/2000000000 : ℝ)|^71 ≤ (24159511601521/100000000000000 : ℝ)^55
        have hw : |(-665488469/2000000000 : ℝ)|=(665488469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2934772497/5000000000 : ℝ)|^71 ≤ (12566935083607/25000000000000 : ℝ)^55
        have hw : |(-2934772497/5000000000 : ℝ)|=(2934772497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (206979911/250000000 : ℝ)*x 0 + (-757178233/10000000000 : ℝ)*x 1 + (663973429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206979911/250000000 : ℝ)^71 ≤ (78366455704391/100000000000000 : ℝ)^55 := by
    have hnat : (206979911 : ℕ)^71*100000000000000^55 ≤ 78366455704391^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206979911 250000000 78366455704391 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757178233/10000000000 : ℝ)^71 ≤ (714787024891/20000000000000 : ℝ)^55 := by
    have hnat : (757178233 : ℕ)^71*20000000000000^55 ≤ 714787024891^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757178233 10000000000 714787024891 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663973429/2500000000 : ℝ)^71 ≤ (4514902288161/25000000000000 : ℝ)^55 := by
    have hnat : (663973429 : ℕ)^71*25000000000000^55 ≤ 4514902288161^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663973429 2500000000 4514902288161 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206979911/250000000 : ℝ), (-757178233/10000000000 : ℝ), (663973429/2500000000 : ℝ)] ![(78366455704391/100000000000000 : ℝ), (714787024891/20000000000000 : ℝ), (4514902288161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206979911/250000000 : ℝ)|^71 ≤ (78366455704391/100000000000000 : ℝ)^55
        have hw : |(206979911/250000000 : ℝ)|=(206979911/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-757178233/10000000000 : ℝ)|^71 ≤ (714787024891/20000000000000 : ℝ)^55
        have hw : |(-757178233/10000000000 : ℝ)|=(757178233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(663973429/2500000000 : ℝ)|^71 ≤ (4514902288161/25000000000000 : ℝ)^55
        have hw : |(663973429/2500000000 : ℝ)|=(663973429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1636716919/5000000000 : ℝ)*x 0 + (-2739492031/5000000000 : ℝ)*x 1 + (992728323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1636716919/5000000000 : ℝ)^71 ≤ (11827247921139/50000000000000 : ℝ)^55 := by
    have hnat : (1636716919 : ℕ)^71*50000000000000^55 ≤ 11827247921139^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636716919 5000000000 11827247921139 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739492031/5000000000 : ℝ)^71 ≤ (5749042450421/12500000000000 : ℝ)^55 := by
    have hnat : (2739492031 : ℕ)^71*12500000000000^55 ≤ 5749042450421^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739492031 5000000000 5749042450421 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992728323/2500000000 : ℝ)^71 ≤ (1214126581393/4000000000000 : ℝ)^55 := by
    have hnat : (992728323 : ℕ)^71*4000000000000^55 ≤ 1214126581393^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992728323 2500000000 1214126581393 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1636716919/5000000000 : ℝ), (-2739492031/5000000000 : ℝ), (992728323/2500000000 : ℝ)] ![(11827247921139/50000000000000 : ℝ), (5749042450421/12500000000000 : ℝ), (1214126581393/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1636716919/5000000000 : ℝ)|^71 ≤ (11827247921139/50000000000000 : ℝ)^55
        have hw : |(-1636716919/5000000000 : ℝ)|=(1636716919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2739492031/5000000000 : ℝ)|^71 ≤ (5749042450421/12500000000000 : ℝ)^55
        have hw : |(-2739492031/5000000000 : ℝ)|=(2739492031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(992728323/2500000000 : ℝ)|^71 ≤ (1214126581393/4000000000000 : ℝ)^55
        have hw : |(992728323/2500000000 : ℝ)|=(992728323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (655217243/1250000000 : ℝ)*x 0 + (3362812863/10000000000 : ℝ)*x 1 + (1035969931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655217243/1250000000 : ℝ)^71 ≤ (43437829967597/100000000000000 : ℝ)^55 := by
    have hnat : (655217243 : ℕ)^71*100000000000000^55 ≤ 43437829967597^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655217243 1250000000 43437829967597 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3362812863/10000000000 : ℝ)^71 ≤ (6122886674151/25000000000000 : ℝ)^55 := by
    have hnat : (3362812863 : ℕ)^71*25000000000000^55 ≤ 6122886674151^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362812863 10000000000 6122886674151 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035969931/2500000000 : ℝ)^71 ≤ (32070623319583/100000000000000 : ℝ)^55 := by
    have hnat : (1035969931 : ℕ)^71*100000000000000^55 ≤ 32070623319583^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035969931 2500000000 32070623319583 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655217243/1250000000 : ℝ), (3362812863/10000000000 : ℝ), (1035969931/2500000000 : ℝ)] ![(43437829967597/100000000000000 : ℝ), (6122886674151/25000000000000 : ℝ), (32070623319583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655217243/1250000000 : ℝ)|^71 ≤ (43437829967597/100000000000000 : ℝ)^55
        have hw : |(655217243/1250000000 : ℝ)|=(655217243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3362812863/10000000000 : ℝ)|^71 ≤ (6122886674151/25000000000000 : ℝ)^55
        have hw : |(3362812863/10000000000 : ℝ)|=(3362812863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035969931/2500000000 : ℝ)|^71 ≤ (32070623319583/100000000000000 : ℝ)^55
        have hw : |(1035969931/2500000000 : ℝ)|=(1035969931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4008508223/10000000000 : ℝ)*x 0 + (-3919811539/10000000000 : ℝ)*x 1 + (-194504479/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4008508223/10000000000 : ℝ)^71 ≤ (120018140749/390625000000 : ℝ)^55 := by
    have hnat : (4008508223 : ℕ)^71*390625000000^55 ≤ 120018140749^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008508223 10000000000 120018140749 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3919811539/10000000000 : ℝ)^71 ≤ (1865616395139/6250000000000 : ℝ)^55 := by
    have hnat : (3919811539 : ℕ)^71*6250000000000^55 ≤ 1865616395139^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3919811539 10000000000 1865616395139 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194504479/400000000 : ℝ)^71 ≤ (9856373408911/25000000000000 : ℝ)^55 := by
    have hnat : (194504479 : ℕ)^71*25000000000000^55 ≤ 9856373408911^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194504479 400000000 9856373408911 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4008508223/10000000000 : ℝ), (-3919811539/10000000000 : ℝ), (-194504479/400000000 : ℝ)] ![(120018140749/390625000000 : ℝ), (1865616395139/6250000000000 : ℝ), (9856373408911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4008508223/10000000000 : ℝ)|^71 ≤ (120018140749/390625000000 : ℝ)^55
        have hw : |(4008508223/10000000000 : ℝ)|=(4008508223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3919811539/10000000000 : ℝ)|^71 ≤ (1865616395139/6250000000000 : ℝ)^55
        have hw : |(-3919811539/10000000000 : ℝ)|=(3919811539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194504479/400000000 : ℝ)|^71 ≤ (9856373408911/25000000000000 : ℝ)^55
        have hw : |(-194504479/400000000 : ℝ)|=(194504479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310085_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (149121363/312500000 : ℝ)*x 0 + (-4247783231/10000000000 : ℝ)*x 1 + (3772434253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149121363/312500000 : ℝ)^71 ≤ (38478470186721/100000000000000 : ℝ)^55 := by
    have hnat : (149121363 : ℕ)^71*100000000000000^55 ≤ 38478470186721^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149121363 312500000 38478470186721 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247783231/10000000000 : ℝ)^71 ≤ (331124558513/1000000000000 : ℝ)^55 := by
    have hnat : (4247783231 : ℕ)^71*1000000000000^55 ≤ 331124558513^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247783231 10000000000 331124558513 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3772434253/10000000000 : ℝ)^71 ≤ (28409073944989/100000000000000 : ℝ)^55 := by
    have hnat : (3772434253 : ℕ)^71*100000000000000^55 ≤ 28409073944989^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772434253 10000000000 28409073944989 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(149121363/312500000 : ℝ), (-4247783231/10000000000 : ℝ), (3772434253/10000000000 : ℝ)] ![(38478470186721/100000000000000 : ℝ), (331124558513/1000000000000 : ℝ), (28409073944989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(149121363/312500000 : ℝ)|^71 ≤ (38478470186721/100000000000000 : ℝ)^55
        have hw : |(149121363/312500000 : ℝ)|=(149121363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4247783231/10000000000 : ℝ)|^71 ≤ (331124558513/1000000000000 : ℝ)^55
        have hw : |(-4247783231/10000000000 : ℝ)|=(4247783231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3772434253/10000000000 : ℝ)|^71 ≤ (28409073944989/100000000000000 : ℝ)^55
        have hw : |(3772434253/10000000000 : ℝ)|=(3772434253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310085 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2014212001/10000000000 : ℝ)*X 0 0+(-367045457/500000000 : ℝ)*X 0 1+(2904024207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5592715259/10000000000 : ℝ)*X 1 0+(2773942679/10000000000 : ℝ)*X 1 1+(1075747967/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-804440817/5000000000 : ℝ)*X 0 0+(-4029806379/5000000000 : ℝ)*X 0 1+(22823971/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2835756629/5000000000 : ℝ)*X 1 0+(322032473/1250000000 : ℝ)*X 1 1+(4389668667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2057341003/5000000000 : ℝ)*X 2 0+(-1342216883/5000000000 : ℝ)*X 2 1+(-1459296023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1519612033/2500000000 : ℝ)*X 0 0+(-1631938203/10000000000 : ℝ)*X 0 1+(2352315167/5000000000 : ℝ)*X 0 2+(1519612033/2500000000 : ℝ)*X 1 0+(-1631938203/10000000000 : ℝ)*X 1 1+(2352315167/5000000000 : ℝ)*X 1 2+(1519612033/2500000000 : ℝ)*X 2 0+(-1631938203/10000000000 : ℝ)*X 2 1+(2352315167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-76226649/400000000 : ℝ)*X 0 0+(-1481487589/2000000000 : ℝ)*X 0 1+(2913585313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2379494251/5000000000 : ℝ)*X 1 0+(2938123543/10000000000 : ℝ)*X 1 1+(2510039103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2044164063/5000000000 : ℝ)*X 2 0+(-46626277/156250000 : ℝ)*X 2 1+(-5616922169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8316436189/10000000000 : ℝ)*X 0 0+(-1434929231/10000000000 : ℝ)*X 0 1+(2061387471/10000000000 : ℝ)*X 0 2+(8316436189/10000000000 : ℝ)*X 1 0+(-1434929231/10000000000 : ℝ)*X 1 1+(2061387471/10000000000 : ℝ)*X 1 2+(8316436189/10000000000 : ℝ)*X 2 0+(-1434929231/10000000000 : ℝ)*X 2 1+(2061387471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-696709697/5000000000 : ℝ)*X 0 0+(-3994047179/5000000000 : ℝ)*X 0 1+(642759969/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1559199779/2500000000 : ℝ)*X 1 0+(1262907379/5000000000 : ℝ)*X 1 1+(3803314251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1738625393/5000000000 : ℝ)*X 2 0+(-665488469/2000000000 : ℝ)*X 2 1+(-2934772497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((206979911/250000000 : ℝ)*X 0 0+(-757178233/10000000000 : ℝ)*X 0 1+(663973429/2500000000 : ℝ)*X 0 2+(206979911/250000000 : ℝ)*X 1 0+(-757178233/10000000000 : ℝ)*X 1 1+(663973429/2500000000 : ℝ)*X 1 2+(206979911/250000000 : ℝ)*X 2 0+(-757178233/10000000000 : ℝ)*X 2 1+(663973429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2109/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2109/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1289322289249922895921/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2790246587249/1000000000000 : ℝ)*(base3) + (532355446931/500000000000 : ℝ)*(base40) + (23148159309/1000000000000 : ℝ)*(base49) + (2315525920567/1000000000000 : ℝ)*(base50) + (180578337569/40000000000 : ℝ)*(major_s0_0) + (180578337569/40000000000 : ℝ)*(major_s0_1) + (180578337569/40000000000 : ℝ)*(major_s0_2) + (6238641536819/1000000000000 : ℝ)*(sp_s0_7) + (4514411204581/500000000000 : ℝ)*(sp_s0_8) + (6238561549239/1000000000000 : ℝ)*(sp_s0_9) + (21495563/1000000000000 : ℝ)*(sp_s0_13) + (34337989/500000000000 : ℝ)*(sp_s0_15) + (2961073/1000000000000 : ℝ)*(sp_s0_21) + (20737163/250000000000 : ℝ)*(sp_s0_23) + (2790268082813/1000000000000 : ℝ)*(f.failure) + (6238644497891/1000000000000 : ℝ)*(f.sum) + (24750662508841/100000000000000000000000000 : ℝ)*base63 + (365915341289329/400000000000000000000000000 : ℝ)*base65 + (232899190244693/400000000000000000000000000 : ℝ)*base66 + (75431471924693/400000000000000000000000000 : ℝ)*base69 + (5431411992989/200000000000000000000000000 : ℝ)*base70 + (116640085150671/400000000000000000000000000 : ℝ)*base73 + (14147981169329/400000000000000000000000000 : ℝ)*base74 + (4882646764693/400000000000000000000000000 : ℝ)*base77 + (19857622787011/200000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (63709/100000000000000000 : ℝ)*base87 + (63709/100000000000000000 : ℝ)*base89 + (63709/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-6571/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-6571/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33609100484838283030611/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111057974857/100000000000 : ℝ)*(base40) + (6600746419/50000000000 : ℝ)*(base50) + (62982205527/500000000000 : ℝ)*(base59) + (3795123077323/1000000000000 : ℝ)*(major_s0_0) + (3795123077323/1000000000000 : ℝ)*(major_s0_1) + (3795123077323/1000000000000 : ℝ)*(major_s0_2) + (91380059/500000000000 : ℝ)*(sp_s0_0) + (4942041/200000000000 : ℝ)*(sp_s0_1) + (12931791/1000000000000 : ℝ)*(sp_s0_7) + (401258027/1000000000000 : ℝ)*(sp_s0_9) + (5244380175631/1000000000000 : ℝ)*(sp_s0_14) + (1048910231467/200000000000 : ℝ)*(sp_s0_15) + (5244174609513/1000000000000 : ℝ)*(sp_s0_16) + (234566580589/100000000000 : ℝ)*(sp_s0_20) + (234566580589/100000000000 : ℝ)*(f.failure) + (262228793377/50000000000 : ℝ)*(f.sum) + (135365445820147/2500000000000000000000000000 : ℝ)*base63 + (1066316116546757/10000000000000000000000000000 : ℝ)*base64 + (1977929474266169/10000000000000000000000000000 : ℝ)*base67 + (4666257168266169/10000000000000000000000000000 : ℝ)*base68 + (1502251651406463/5000000000000000000000000000 : ℝ)*base70 + (2432085040453243/10000000000000000000000000000 : ℝ)*base72 + (956304910453243/10000000000000000000000000000 : ℝ)*base74 + (1962165042733831/10000000000000000000000000000 : ℝ)*base77 + (1668096391906463/5000000000000000000000000000 : ℝ)*base79 + (6077/10000000000000000 : ℝ)*base87 + (6077/10000000000000000 : ℝ)*base89 + (6077/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37879/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37879/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (915236498399390460543/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (368125492623/250000000000 : ℝ)*(base3) + (2183828712277/1000000000000 : ℝ)*(base40) + (2002013749677/1000000000000 : ℝ)*(base50) + (63156534977/500000000000 : ℝ)*(base59) + (6441854413817/1000000000000 : ℝ)*(major_s0_0) + (6441854413817/1000000000000 : ℝ)*(major_s0_1) + (6441854413817/1000000000000 : ℝ)*(major_s0_2) + (65058053/500000000000 : ℝ)*(sp_s0_7) + (7442869/1000000000000 : ℝ)*(sp_s0_14) + (2278729/62500000000 : ℝ)*(sp_s0_20) + (8902027961717/1000000000000 : ℝ)*(sp_s0_21) + (2074933498237/200000000000 : ℝ)*(sp_s0_22) + (8902165520693/1000000000000 : ℝ)*(sp_s0_23) + (1254501218073/500000000000 : ℝ)*(sp_s0_27) + (3981540866303/1000000000000 : ℝ)*(f.failure) + (8902165520693/1000000000000 : ℝ)*(f.sum) + (1049496290203313/2500000000000000000000000000 : ℝ)*base63 + (8995490878376503/10000000000000000000000000000 : ℝ)*base64 + (6153595880563251/10000000000000000000000000000 : ℝ)*base67 + (5251479954436749/10000000000000000000000000000 : ℝ)*base69 + (1342031598469877/5000000000000000000000000000 : ℝ)*base70 + (4595470804376503/10000000000000000000000000000 : ℝ)*base73 + (6089561085376503/10000000000000000000000000000 : ℝ)*base75 + (3572233362563251/10000000000000000000000000000 : ℝ)*base76 + (2854117965469877/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (61279/100000000000000000 : ℝ)*base87 + (61279/100000000000000000 : ℝ)*base89 + (61279/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (2109/12500 : ℝ) ^ (35/8 : ℝ) ≤ (41577055522570937/100000000000000000000 : ℝ) := by
    have hpowers : (2109/12500 : ℝ)^35 ≤ (41577055522570937/100000000000000000000 : ℝ)^8 := by
      have hnat : (2109 : ℕ)^35*100000000000000000000^8 ≤ 41577055522570937^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2109 12500 41577055522570937 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2109/12500 : ℝ)) (X := (41577055522570937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100041577055522570937/100000000000000000000 : ℝ) ≤ (10000950180331499/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100041577055522570937/100000000000000000000 : ℝ)^8 ≤ (10000950180331499/10000000000000000 : ℝ)^35 := by
      have hnat : (100041577055522570937 : ℕ)^8*10000000000000000^35 ≤ 10000950180331499^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041577055522570937 100000000000000000000 10000950180331499 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000950180331499/10000000000000000 : ℝ)) (X := (100041577055522570937/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50041577055522570937/50000000000000000000 : ℝ) ≤ (1000190005608021/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50041577055522570937/50000000000000000000 : ℝ)^8 ≤ (1000190005608021/1000000000000000 : ℝ)^35 := by
      have hnat : (50041577055522570937 : ℕ)^8*1000000000000000^35 ≤ 1000190005608021^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041577055522570937 50000000000000000000 1000190005608021 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000190005608021/1000000000000000 : ℝ)) (X := (50041577055522570937/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(950180331499/1687200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(949875748711/1687200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2109/12500 : ℝ)) (alpha := (950180331499/1687200000000000 : ℝ)) (beta := (949875748711/1687200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2109/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(950180331499/1687200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(949875748711/1687200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6571/50000 : ℝ) ^ (35/8 : ℝ) ≤ (6968092453732417/50000000000000000000 : ℝ) := by
    have hpowers : (6571/50000 : ℝ)^35 ≤ (6968092453732417/50000000000000000000 : ℝ)^8 := by
      have hnat : (6571 : ℕ)^35*50000000000000000000^8 ≤ 6968092453732417^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6571 50000 6968092453732417 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6571/50000 : ℝ)) (X := (6968092453732417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50006968092453732417/50000000000000000000 : ℝ) ≤ (1250039815530987/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50006968092453732417/50000000000000000000 : ℝ)^8 ≤ (1250039815530987/1250000000000000 : ℝ)^35 := by
      have hnat : (50006968092453732417 : ℕ)^8*1250000000000000^35 ≤ 1250039815530987^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006968092453732417 50000000000000000000 1250039815530987 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250039815530987/1250000000000000 : ℝ)) (X := (50006968092453732417/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25006968092453732417/25000000000000000000 : ℝ) ≤ (1000063701425859/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25006968092453732417/25000000000000000000 : ℝ)^8 ≤ (1000063701425859/1000000000000000 : ℝ)^35 := by
      have hnat : (25006968092453732417 : ℕ)^8*1000000000000000^35 ≤ 1000063701425859^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006968092453732417 25000000000000000000 1000063701425859 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000063701425859/1000000000000000 : ℝ)) (X := (25006968092453732417/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(39815530987/164275000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(159245005347/657100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (6571/50000 : ℝ)) (alpha := (39815530987/164275000000000 : ℝ)) (beta := (159245005347/657100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (6571/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(39815530987/164275000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(159245005347/657100000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37879/100000 : ℝ) ^ (35/8 : ℝ) ≤ (715259219520504647/50000000000000000000 : ℝ) := by
    have hpowers : (37879/100000 : ℝ)^35 ≤ (715259219520504647/50000000000000000000 : ℝ)^8 := by
      have hnat : (37879 : ℕ)^35*50000000000000000000^8 ≤ 715259219520504647^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37879 100000 715259219520504647 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37879/100000 : ℝ)) (X := (715259219520504647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50715259219520504647/50000000000000000000 : ℝ) ≤ (501625932875941/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50715259219520504647/50000000000000000000 : ℝ)^8 ≤ (501625932875941/500000000000000 : ℝ)^35 := by
      have hnat : (50715259219520504647 : ℕ)^8*500000000000000^35 ≤ 501625932875941^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50715259219520504647 50000000000000000000 501625932875941 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501625932875941/500000000000000 : ℝ)) (X := (50715259219520504647/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25715259219520504647/25000000000000000000 : ℝ) ≤ (1258085677553727/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25715259219520504647/25000000000000000000 : ℝ)^8 ≤ (1258085677553727/1250000000000000 : ℝ)^35 := by
      have hnat : (25715259219520504647 : ℕ)^8*1250000000000000^35 ≤ 1258085677553727^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25715259219520504647 25000000000000000000 1258085677553727 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258085677553727/1250000000000000 : ℝ)) (X := (25715259219520504647/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1625932875941/189395000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8041690727749/946975000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (37879/100000 : ℝ)) (alpha := (1625932875941/189395000000000 : ℝ)) (beta := (8041690727749/946975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37879/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1625932875941/189395000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8041690727749/946975000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1636716919/5000000000 : ℝ)*X 0 0+(-2739492031/5000000000 : ℝ)*X 0 1+(992728323/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((655217243/1250000000 : ℝ)*X 1 0+(3362812863/10000000000 : ℝ)*X 1 1+(1035969931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4008508223/10000000000 : ℝ)*X 2 0+(-3919811539/10000000000 : ℝ)*X 2 1+(-194504479/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((149121363/312500000 : ℝ)*X 0 0+(-4247783231/10000000000 : ℝ)*X 0 1+(3772434253/10000000000 : ℝ)*X 0 2+(149121363/312500000 : ℝ)*X 1 0+(-4247783231/10000000000 : ℝ)*X 1 1+(3772434253/10000000000 : ℝ)*X 1 2+(149121363/312500000 : ℝ)*X 2 0+(-4247783231/10000000000 : ℝ)*X 2 1+(3772434253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-7226942812869775481497127598501/1093617156418750000000000000000 : ℝ) := by norm_num
    linear_combination (7541/1000000000000 : ℝ)*(base1) + (19/7812500000 : ℝ)*(base22) + (11641/1000000000000 : ℝ)*(base24) + (347/500000000000 : ℝ)*(base39) + (20549898937/62500000000 : ℝ)*(base40) + (13430245913/125000000000 : ℝ)*(base49) + (365595792027/1000000000000 : ℝ)*(base50) + (703/500000000000 : ℝ)*(base59) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2202764405921/1000000000000 : ℝ)*(sp_s1_0) + (2202764398379/1000000000000 : ℝ)*(sp_s1_1) + (2202764384307/1000000000000 : ℝ)*(sp_s1_2) + (999999992459/1000000000000 : ℝ)*(sp_s1_6) + (2202764398379/1000000000000 : ℝ)*(f.sum) + (598661592310907957/1244514545000000000000000000000 : ℝ)*base62 + (211107030556149/378790000000000000000000000 : ℝ)*base65 + (12696969087689/65710000000000000000000000 : ℝ)*base66 + (1126719390673/9469750000000000000000000 : ℝ)*base69 + (33704240447751003/33286171250000000000000000000 : ℝ)*base71 + (5413897837669/7030000000000000000000000 : ℝ)*base72 + (8769482243011/13142000000000000000000000 : ℝ)*base74 + (2194469948453/3515000000000000000000000 : ℝ)*base77 + (11227170589783613/23097065000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b037 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c310085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b037 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
