-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:16:40.426237+00:00
-- url     : https://prove2.me/submissions/5a8baf98-9237-4678-b959-c5fbb4bd16ef

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310080_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310080 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c310080_s0 p hpa hpb X hX
  have h1 := collision_c310080_s1 p hpa hpb X hX h0
  exact collision_c310080_s2 p hpa hpb X hX h1

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
theorem collision_support_c310079_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8046888769/10000000000 : ℝ)*x 0 + (-191116071/1250000000 : ℝ)*x 1 + (-296493013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8046888769/10000000000 : ℝ)^71 ≤ (75539538098549/100000000000000 : ℝ)^55 := by
    have hnat : (8046888769 : ℕ)^71*100000000000000^55 ≤ 75539538098549^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8046888769 10000000000 75539538098549 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191116071/1250000000 : ℝ)^71 ≤ (8853561655623/100000000000000 : ℝ)^55 := by
    have hnat : (191116071 : ℕ)^71*100000000000000^55 ≤ 8853561655623^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191116071 1250000000 8853561655623 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296493013/1250000000 : ℝ)^71 ≤ (3121380047067/20000000000000 : ℝ)^55 := by
    have hnat : (296493013 : ℕ)^71*20000000000000^55 ≤ 3121380047067^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296493013 1250000000 3121380047067 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8046888769/10000000000 : ℝ), (-191116071/1250000000 : ℝ), (-296493013/1250000000 : ℝ)] ![(75539538098549/100000000000000 : ℝ), (8853561655623/100000000000000 : ℝ), (3121380047067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8046888769/10000000000 : ℝ)|^71 ≤ (75539538098549/100000000000000 : ℝ)^55
        have hw : |(8046888769/10000000000 : ℝ)|=(8046888769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191116071/1250000000 : ℝ)|^71 ≤ (8853561655623/100000000000000 : ℝ)^55
        have hw : |(-191116071/1250000000 : ℝ)|=(191116071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-296493013/1250000000 : ℝ)|^71 ≤ (3121380047067/20000000000000 : ℝ)^55
        have hw : |(-296493013/1250000000 : ℝ)|=(296493013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1587001963/5000000000 : ℝ)*x 0 + (2991130797/5000000000 : ℝ)*x 1 + (3496069181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1587001963/5000000000 : ℝ)^71 ≤ (5682776128191/25000000000000 : ℝ)^55 := by
    have hnat : (1587001963 : ℕ)^71*25000000000000^55 ≤ 5682776128191^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587001963 5000000000 5682776128191 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991130797/5000000000 : ℝ)^71 ≤ (51517350140113/100000000000000 : ℝ)^55 := by
    have hnat : (2991130797 : ℕ)^71*100000000000000^55 ≤ 51517350140113^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991130797 5000000000 51517350140113 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3496069181/10000000000 : ℝ)^71 ≤ (25751545335171/100000000000000 : ℝ)^55 := by
    have hnat : (3496069181 : ℕ)^71*100000000000000^55 ≤ 25751545335171^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3496069181 10000000000 25751545335171 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1587001963/5000000000 : ℝ), (2991130797/5000000000 : ℝ), (3496069181/10000000000 : ℝ)] ![(5682776128191/25000000000000 : ℝ), (51517350140113/100000000000000 : ℝ), (25751545335171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1587001963/5000000000 : ℝ)|^71 ≤ (5682776128191/25000000000000 : ℝ)^55
        have hw : |(1587001963/5000000000 : ℝ)|=(1587001963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2991130797/5000000000 : ℝ)|^71 ≤ (51517350140113/100000000000000 : ℝ)^55
        have hw : |(2991130797/5000000000 : ℝ)|=(2991130797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3496069181/10000000000 : ℝ)|^71 ≤ (25751545335171/100000000000000 : ℝ)^55
        have hw : |(3496069181/10000000000 : ℝ)|=(3496069181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-69376993/400000000 : ℝ)*x 0 + (2966011491/10000000000 : ℝ)*x 1 + (-467568149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69376993/400000000 : ℝ)^71 ≤ (10418828603431/100000000000000 : ℝ)^55 := by
    have hnat : (69376993 : ℕ)^71*100000000000000^55 ≤ 10418828603431^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69376993 400000000 10418828603431 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966011491/10000000000 : ℝ)^71 ≤ (4165365374239/20000000000000 : ℝ)^55 := by
    have hnat : (2966011491 : ℕ)^71*20000000000000^55 ≤ 4165365374239^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966011491 10000000000 4165365374239 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467568149/625000000 : ℝ)^71 ≤ (17188586126517/25000000000000 : ℝ)^55 := by
    have hnat : (467568149 : ℕ)^71*25000000000000^55 ≤ 17188586126517^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467568149 625000000 17188586126517 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69376993/400000000 : ℝ), (2966011491/10000000000 : ℝ), (-467568149/625000000 : ℝ)] ![(10418828603431/100000000000000 : ℝ), (4165365374239/20000000000000 : ℝ), (17188586126517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69376993/400000000 : ℝ)|^71 ≤ (10418828603431/100000000000000 : ℝ)^55
        have hw : |(-69376993/400000000 : ℝ)|=(69376993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2966011491/10000000000 : ℝ)|^71 ≤ (4165365374239/20000000000000 : ℝ)^55
        have hw : |(2966011491/10000000000 : ℝ)|=(2966011491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467568149/625000000 : ℝ)|^71 ≤ (17188586126517/25000000000000 : ℝ)^55
        have hw : |(-467568149/625000000 : ℝ)|=(467568149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (804253129/1000000000 : ℝ)*x 0 + (-63038963/2000000000 : ℝ)*x 1 + (-3241855461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804253129/1000000000 : ℝ)^71 ≤ (3019469479429/4000000000000 : ℝ)^55 := by
    have hnat : (804253129 : ℕ)^71*4000000000000^55 ≤ 3019469479429^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804253129 1000000000 3019469479429 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63038963/2000000000 : ℝ)^71 ≤ (1152927678027/100000000000000 : ℝ)^55 := by
    have hnat : (63038963 : ℕ)^71*100000000000000^55 ≤ 1152927678027^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63038963 2000000000 1152927678027 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3241855461/10000000000 : ℝ)^71 ≤ (23360335329109/100000000000000 : ℝ)^55 := by
    have hnat : (3241855461 : ℕ)^71*100000000000000^55 ≤ 23360335329109^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241855461 10000000000 23360335329109 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804253129/1000000000 : ℝ), (-63038963/2000000000 : ℝ), (-3241855461/10000000000 : ℝ)] ![(3019469479429/4000000000000 : ℝ), (1152927678027/100000000000000 : ℝ), (23360335329109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804253129/1000000000 : ℝ)|^71 ≤ (3019469479429/4000000000000 : ℝ)^55
        have hw : |(804253129/1000000000 : ℝ)|=(804253129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63038963/2000000000 : ℝ)|^71 ≤ (1152927678027/100000000000000 : ℝ)^55
        have hw : |(-63038963/2000000000 : ℝ)|=(63038963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3241855461/10000000000 : ℝ)|^71 ≤ (23360335329109/100000000000000 : ℝ)^55
        have hw : |(-3241855461/10000000000 : ℝ)|=(3241855461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1478201919/10000000000 : ℝ)*x 0 + (975560109/1250000000 : ℝ)*x 1 + (1376069407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1478201919/10000000000 : ℝ)^71 ≤ (8476211117257/100000000000000 : ℝ)^55 := by
    have hnat : (1478201919 : ℕ)^71*100000000000000^55 ≤ 8476211117257^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478201919 10000000000 8476211117257 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975560109/1250000000 : ℝ)^71 ≤ (36307464530477/50000000000000 : ℝ)^55 := by
    have hnat : (975560109 : ℕ)^71*50000000000000^55 ≤ 36307464530477^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975560109 1250000000 36307464530477 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376069407/5000000000 : ℝ)^71 ≤ (18908859807833/100000000000000 : ℝ)^55 := by
    have hnat : (1376069407 : ℕ)^71*100000000000000^55 ≤ 18908859807833^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376069407 5000000000 18908859807833 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1478201919/10000000000 : ℝ), (975560109/1250000000 : ℝ), (1376069407/5000000000 : ℝ)] ![(8476211117257/100000000000000 : ℝ), (36307464530477/50000000000000 : ℝ), (18908859807833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1478201919/10000000000 : ℝ)|^71 ≤ (8476211117257/100000000000000 : ℝ)^55
        have hw : |(1478201919/10000000000 : ℝ)|=(1478201919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(975560109/1250000000 : ℝ)|^71 ≤ (36307464530477/50000000000000 : ℝ)^55
        have hw : |(975560109/1250000000 : ℝ)|=(975560109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376069407/5000000000 : ℝ)|^71 ≤ (18908859807833/100000000000000 : ℝ)^55
        have hw : |(1376069407/5000000000 : ℝ)|=(1376069407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (477638691/2000000000 : ℝ)*x 0 + (1893138903/2500000000 : ℝ)*x 1 + (-2230197063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477638691/2000000000 : ℝ)^71 ≤ (15745058136031/100000000000000 : ℝ)^55 := by
    have hnat : (477638691 : ℕ)^71*100000000000000^55 ≤ 15745058136031^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477638691 2000000000 15745058136031 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893138903/2500000000 : ℝ)^71 ≤ (69841411606087/100000000000000 : ℝ)^55 := by
    have hnat : (1893138903 : ℕ)^71*100000000000000^55 ≤ 69841411606087^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893138903 2500000000 69841411606087 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230197063/10000000000 : ℝ)^71 ≤ (14413530245853/100000000000000 : ℝ)^55 := by
    have hnat : (2230197063 : ℕ)^71*100000000000000^55 ≤ 14413530245853^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230197063 10000000000 14413530245853 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(477638691/2000000000 : ℝ), (1893138903/2500000000 : ℝ), (-2230197063/10000000000 : ℝ)] ![(15745058136031/100000000000000 : ℝ), (69841411606087/100000000000000 : ℝ), (14413530245853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(477638691/2000000000 : ℝ)|^71 ≤ (15745058136031/100000000000000 : ℝ)^55
        have hw : |(477638691/2000000000 : ℝ)|=(477638691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1893138903/2500000000 : ℝ)|^71 ≤ (69841411606087/100000000000000 : ℝ)^55
        have hw : |(1893138903/2500000000 : ℝ)|=(1893138903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230197063/10000000000 : ℝ)|^71 ≤ (14413530245853/100000000000000 : ℝ)^55
        have hw : |(-2230197063/10000000000 : ℝ)|=(2230197063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-317021121/10000000000 : ℝ)*x 0 + (1788000899/5000000000 : ℝ)*x 1 + (-243133609/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317021121/10000000000 : ℝ)^71 ≤ (232311721521/20000000000000 : ℝ)^55 := by
    have hnat : (317021121 : ℕ)^71*20000000000000^55 ≤ 232311721521^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317021121 10000000000 232311721521 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788000899/5000000000 : ℝ)^71 ≤ (207141491033/781250000000 : ℝ)^55 := by
    have hnat : (1788000899 : ℕ)^71*781250000000^55 ≤ 207141491033^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788000899 5000000000 207141491033 781250000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243133609/312500000 : ℝ)^71 ≤ (14464866104669/20000000000000 : ℝ)^55 := by
    have hnat : (243133609 : ℕ)^71*20000000000000^55 ≤ 14464866104669^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243133609 312500000 14464866104669 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-317021121/10000000000 : ℝ), (1788000899/5000000000 : ℝ), (-243133609/312500000 : ℝ)] ![(232311721521/20000000000000 : ℝ), (207141491033/781250000000 : ℝ), (14464866104669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-317021121/10000000000 : ℝ)|^71 ≤ (232311721521/20000000000000 : ℝ)^55
        have hw : |(-317021121/10000000000 : ℝ)|=(317021121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1788000899/5000000000 : ℝ)|^71 ≤ (207141491033/781250000000 : ℝ)^55
        have hw : |(1788000899/5000000000 : ℝ)|=(1788000899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243133609/312500000 : ℝ)|^71 ≤ (14464866104669/20000000000000 : ℝ)^55
        have hw : |(-243133609/312500000 : ℝ)|=(243133609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2294964269/2500000000 : ℝ)*x 0 + (-253815473/2000000000 : ℝ)*x 1 + (-744562693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2294964269/2500000000 : ℝ)^71 ≤ (89541538210897/100000000000000 : ℝ)^55 := by
    have hnat : (2294964269 : ℕ)^71*100000000000000^55 ≤ 89541538210897^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294964269 2500000000 89541538210897 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253815473/2000000000 : ℝ)^71 ≤ (6961208404421/100000000000000 : ℝ)^55 := by
    have hnat : (253815473 : ℕ)^71*100000000000000^55 ≤ 6961208404421^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253815473 2000000000 6961208404421 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (744562693/10000000000 : ℝ)^71 ≤ (3497253360813/100000000000000 : ℝ)^55 := by
    have hnat : (744562693 : ℕ)^71*100000000000000^55 ≤ 3497253360813^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744562693 10000000000 3497253360813 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2294964269/2500000000 : ℝ), (-253815473/2000000000 : ℝ), (-744562693/10000000000 : ℝ)] ![(89541538210897/100000000000000 : ℝ), (6961208404421/100000000000000 : ℝ), (3497253360813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2294964269/2500000000 : ℝ)|^71 ≤ (89541538210897/100000000000000 : ℝ)^55
        have hw : |(2294964269/2500000000 : ℝ)|=(2294964269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253815473/2000000000 : ℝ)|^71 ≤ (6961208404421/100000000000000 : ℝ)^55
        have hw : |(-253815473/2000000000 : ℝ)|=(253815473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-744562693/10000000000 : ℝ)|^71 ≤ (3497253360813/100000000000000 : ℝ)^55
        have hw : |(-744562693/10000000000 : ℝ)|=(744562693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1904702383/5000000000 : ℝ)*x 0 + (1465628779/2500000000 : ℝ)*x 1 + (59792177/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904702383/5000000000 : ℝ)^71 ≤ (7192248023143/25000000000000 : ℝ)^55 := by
    have hnat : (1904702383 : ℕ)^71*25000000000000^55 ≤ 7192248023143^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904702383 5000000000 7192248023143 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1465628779/2500000000 : ℝ)^71 ≤ (25095017334113/50000000000000 : ℝ)^55 := by
    have hnat : (1465628779 : ℕ)^71*50000000000000^55 ≤ 25095017334113^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465628779 2500000000 25095017334113 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59792177/200000000 : ℝ)^71 ≤ (21040973223761/100000000000000 : ℝ)^55 := by
    have hnat : (59792177 : ℕ)^71*100000000000000^55 ≤ 21040973223761^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59792177 200000000 21040973223761 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1904702383/5000000000 : ℝ), (1465628779/2500000000 : ℝ), (59792177/200000000 : ℝ)] ![(7192248023143/25000000000000 : ℝ), (25095017334113/50000000000000 : ℝ), (21040973223761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1904702383/5000000000 : ℝ)|^71 ≤ (7192248023143/25000000000000 : ℝ)^55
        have hw : |(1904702383/5000000000 : ℝ)|=(1904702383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1465628779/2500000000 : ℝ)|^71 ≤ (25095017334113/50000000000000 : ℝ)^55
        have hw : |(1465628779/2500000000 : ℝ)|=(1465628779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59792177/200000000 : ℝ)|^71 ≤ (21040973223761/100000000000000 : ℝ)^55
        have hw : |(59792177/200000000 : ℝ)|=(59792177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_17 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999929/10000000000 : ℝ)*x 0 + (2963/5000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999929/10000000000 : ℝ)^71 ≤ (19999999816691/20000000000000 : ℝ)^55 := by
    have hnat : (9999999929 : ℕ)^71*20000000000000^55 ≤ 19999999816691^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999929 10000000000 19999999816691 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963/5000000000 : ℝ)^71 ≤ (457269/50000000000000 : ℝ)^55 := by
    have hnat : (2963 : ℕ)^71*50000000000000^55 ≤ 457269^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963 5000000000 457269 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^71 ≤ (0 : ℝ)^55 := by
    have hnat : (0 : ℕ)^71*1^55 ≤ 0^55*1^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999929/10000000000 : ℝ), (2963/5000000000 : ℝ), (0 : ℝ)] ![(19999999816691/20000000000000 : ℝ), (457269/50000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999929/10000000000 : ℝ)|^71 ≤ (19999999816691/20000000000000 : ℝ)^55
        have hw : |(9999999929/10000000000 : ℝ)|=(9999999929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963/5000000000 : ℝ)|^71 ≤ (457269/50000000000000 : ℝ)^55
        have hw : |(2963/5000000000 : ℝ)|=(2963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^71 ≤ (0 : ℝ)^55
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1303806973/5000000000 : ℝ)*x 0 + (1640145977/5000000000 : ℝ)*x 1 + (-6613908387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1303806973/5000000000 : ℝ)^71 ≤ (17636936964469/100000000000000 : ℝ)^55 := by
    have hnat : (1303806973 : ℕ)^71*100000000000000^55 ≤ 17636936964469^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303806973 5000000000 17636936964469 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1640145977/5000000000 : ℝ)^71 ≤ (4743698075097/20000000000000 : ℝ)^55 := by
    have hnat : (1640145977 : ℕ)^71*20000000000000^55 ≤ 4743698075097^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640145977 5000000000 4743698075097 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6613908387/10000000000 : ℝ)^71 ≤ (14661143161851/25000000000000 : ℝ)^55 := by
    have hnat : (6613908387 : ℕ)^71*25000000000000^55 ≤ 14661143161851^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6613908387 10000000000 14661143161851 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1303806973/5000000000 : ℝ), (1640145977/5000000000 : ℝ), (-6613908387/10000000000 : ℝ)] ![(17636936964469/100000000000000 : ℝ), (4743698075097/20000000000000 : ℝ), (14661143161851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1303806973/5000000000 : ℝ)|^71 ≤ (17636936964469/100000000000000 : ℝ)^55
        have hw : |(1303806973/5000000000 : ℝ)|=(1303806973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1640145977/5000000000 : ℝ)|^71 ≤ (4743698075097/20000000000000 : ℝ)^55
        have hw : |(1640145977/5000000000 : ℝ)|=(1640145977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6613908387/10000000000 : ℝ)|^71 ≤ (14661143161851/25000000000000 : ℝ)^55
        have hw : |(-6613908387/10000000000 : ℝ)|=(6613908387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-446044869/10000000000 : ℝ)*x 0 + (352317347/625000000 : ℝ)*x 1 + (-5888951913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446044869/10000000000 : ℝ)^71 ≤ (360994416541/20000000000000 : ℝ)^55 := by
    have hnat : (446044869 : ℕ)^71*20000000000000^55 ≤ 360994416541^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446044869 10000000000 360994416541 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352317347/625000000 : ℝ)^71 ≤ (47712630183243/100000000000000 : ℝ)^55 := by
    have hnat : (352317347 : ℕ)^71*100000000000000^55 ≤ 47712630183243^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352317347 625000000 47712630183243 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5888951913/10000000000 : ℝ)^71 ≤ (3155149857337/6250000000000 : ℝ)^55 := by
    have hnat : (5888951913 : ℕ)^71*6250000000000^55 ≤ 3155149857337^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5888951913 10000000000 3155149857337 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446044869/10000000000 : ℝ), (352317347/625000000 : ℝ), (-5888951913/10000000000 : ℝ)] ![(360994416541/20000000000000 : ℝ), (47712630183243/100000000000000 : ℝ), (3155149857337/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446044869/10000000000 : ℝ)|^71 ≤ (360994416541/20000000000000 : ℝ)^55
        have hw : |(-446044869/10000000000 : ℝ)|=(446044869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352317347/625000000 : ℝ)|^71 ≤ (47712630183243/100000000000000 : ℝ)^55
        have hw : |(352317347/625000000 : ℝ)|=(352317347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5888951913/10000000000 : ℝ)|^71 ≤ (3155149857337/6250000000000 : ℝ)^55
        have hw : |(-5888951913/10000000000 : ℝ)|=(5888951913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9579671657/10000000000 : ℝ)*x 0 + (-178458387/5000000000 : ℝ)*x 1 + (-208107259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9579671657/10000000000 : ℝ)^71 ≤ (1892149060827/2000000000000 : ℝ)^55 := by
    have hnat : (9579671657 : ℕ)^71*2000000000000^55 ≤ 1892149060827^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9579671657 10000000000 1892149060827 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178458387/5000000000 : ℝ)^71 ≤ (1353616154779/100000000000000 : ℝ)^55 := by
    have hnat : (178458387 : ℕ)^71*100000000000000^55 ≤ 1353616154779^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178458387 5000000000 1353616154779 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208107259/2500000000 : ℝ)^71 ≤ (1009732698831/25000000000000 : ℝ)^55 := by
    have hnat : (208107259 : ℕ)^71*25000000000000^55 ≤ 1009732698831^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208107259 2500000000 1009732698831 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9579671657/10000000000 : ℝ), (-178458387/5000000000 : ℝ), (-208107259/2500000000 : ℝ)] ![(1892149060827/2000000000000 : ℝ), (1353616154779/100000000000000 : ℝ), (1009732698831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9579671657/10000000000 : ℝ)|^71 ≤ (1892149060827/2000000000000 : ℝ)^55
        have hw : |(9579671657/10000000000 : ℝ)|=(9579671657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178458387/5000000000 : ℝ)|^71 ≤ (1353616154779/100000000000000 : ℝ)^55
        have hw : |(-178458387/5000000000 : ℝ)|=(178458387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208107259/2500000000 : ℝ)|^71 ≤ (1009732698831/25000000000000 : ℝ)^55
        have hw : |(-208107259/2500000000 : ℝ)|=(208107259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (515058143/2000000000 : ℝ)*x 0 + (242240897/400000000 : ℝ)*x 1 + (1983064617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515058143/2000000000 : ℝ)^71 ≤ (17355225684417/100000000000000 : ℝ)^55 := by
    have hnat : (515058143 : ℕ)^71*100000000000000^55 ≤ 17355225684417^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515058143 2000000000 17355225684417 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242240897/400000000 : ℝ)^71 ≤ (5233880841253/10000000000000 : ℝ)^55 := by
    have hnat : (242240897 : ℕ)^71*10000000000000^55 ≤ 5233880841253^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242240897 400000000 5233880841253 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983064617/5000000000 : ℝ)^71 ≤ (15152982944777/50000000000000 : ℝ)^55 := by
    have hnat : (1983064617 : ℕ)^71*50000000000000^55 ≤ 15152982944777^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983064617 5000000000 15152982944777 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515058143/2000000000 : ℝ), (242240897/400000000 : ℝ), (1983064617/5000000000 : ℝ)] ![(17355225684417/100000000000000 : ℝ), (5233880841253/10000000000000 : ℝ), (15152982944777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515058143/2000000000 : ℝ)|^71 ≤ (17355225684417/100000000000000 : ℝ)^55
        have hw : |(515058143/2000000000 : ℝ)|=(515058143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242240897/400000000 : ℝ)|^71 ≤ (5233880841253/10000000000000 : ℝ)^55
        have hw : |(242240897/400000000 : ℝ)|=(242240897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1983064617/5000000000 : ℝ)|^71 ≤ (15152982944777/50000000000000 : ℝ)^55
        have hw : |(1983064617/5000000000 : ℝ)|=(1983064617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2092255809/5000000000 : ℝ)*x 0 + (5416449819/10000000000 : ℝ)*x 1 + (-3117168187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092255809/5000000000 : ℝ)^71 ≤ (324771420093/1000000000000 : ℝ)^55 := by
    have hnat : (2092255809 : ℕ)^71*1000000000000^55 ≤ 324771420093^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092255809 5000000000 324771420093 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416449819/10000000000 : ℝ)^71 ≤ (45315827650729/100000000000000 : ℝ)^55 := by
    have hnat : (5416449819 : ℕ)^71*100000000000000^55 ≤ 45315827650729^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416449819 10000000000 45315827650729 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3117168187/10000000000 : ℝ)^71 ≤ (22207030321919/100000000000000 : ℝ)^55 := by
    have hnat : (3117168187 : ℕ)^71*100000000000000^55 ≤ 22207030321919^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117168187 10000000000 22207030321919 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092255809/5000000000 : ℝ), (5416449819/10000000000 : ℝ), (-3117168187/10000000000 : ℝ)] ![(324771420093/1000000000000 : ℝ), (45315827650729/100000000000000 : ℝ), (22207030321919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092255809/5000000000 : ℝ)|^71 ≤ (324771420093/1000000000000 : ℝ)^55
        have hw : |(2092255809/5000000000 : ℝ)|=(2092255809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416449819/10000000000 : ℝ)|^71 ≤ (45315827650729/100000000000000 : ℝ)^55
        have hw : |(5416449819/10000000000 : ℝ)|=(5416449819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3117168187/10000000000 : ℝ)|^71 ≤ (22207030321919/100000000000000 : ℝ)^55
        have hw : |(-3117168187/10000000000 : ℝ)|=(3117168187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1325126329/5000000000 : ℝ)*x 0 + (4413266151/10000000000 : ℝ)*x 1 + (-5590364347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325126329/5000000000 : ℝ)^71 ≤ (18010107508943/100000000000000 : ℝ)^55 := by
    have hnat : (1325126329 : ℕ)^71*100000000000000^55 ≤ 18010107508943^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325126329 5000000000 18010107508943 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413266151/10000000000 : ℝ)^71 ≤ (34787050566731/100000000000000 : ℝ)^55 := by
    have hnat : (4413266151 : ℕ)^71*100000000000000^55 ≤ 34787050566731^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413266151 10000000000 34787050566731 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590364347/10000000000 : ℝ)^71 ≤ (9440568379847/20000000000000 : ℝ)^55 := by
    have hnat : (5590364347 : ℕ)^71*20000000000000^55 ≤ 9440568379847^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590364347 10000000000 9440568379847 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1325126329/5000000000 : ℝ), (4413266151/10000000000 : ℝ), (-5590364347/10000000000 : ℝ)] ![(18010107508943/100000000000000 : ℝ), (34787050566731/100000000000000 : ℝ), (9440568379847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1325126329/5000000000 : ℝ)|^71 ≤ (18010107508943/100000000000000 : ℝ)^55
        have hw : |(-1325126329/5000000000 : ℝ)|=(1325126329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413266151/10000000000 : ℝ)|^71 ≤ (34787050566731/100000000000000 : ℝ)^55
        have hw : |(4413266151/10000000000 : ℝ)|=(4413266151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5590364347/10000000000 : ℝ)|^71 ≤ (9440568379847/20000000000000 : ℝ)^55
        have hw : |(-5590364347/10000000000 : ℝ)|=(5590364347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6422070701/10000000000 : ℝ)*x 0 + (-1401839539/5000000000 : ℝ)*x 1 + (-1664531591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6422070701/10000000000 : ℝ)^71 ≤ (56458068394513/100000000000000 : ℝ)^55 := by
    have hnat : (6422070701 : ℕ)^71*100000000000000^55 ≤ 56458068394513^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6422070701 10000000000 56458068394513 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401839539/5000000000 : ℝ)^71 ≤ (154937815989/800000000000 : ℝ)^55 := by
    have hnat : (1401839539 : ℕ)^71*800000000000^55 ≤ 154937815989^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401839539 5000000000 154937815989 800000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1664531591/5000000000 : ℝ)^71 ≤ (24174704595963/100000000000000 : ℝ)^55 := by
    have hnat : (1664531591 : ℕ)^71*100000000000000^55 ≤ 24174704595963^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664531591 5000000000 24174704595963 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6422070701/10000000000 : ℝ), (-1401839539/5000000000 : ℝ), (-1664531591/5000000000 : ℝ)] ![(56458068394513/100000000000000 : ℝ), (154937815989/800000000000 : ℝ), (24174704595963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6422070701/10000000000 : ℝ)|^71 ≤ (56458068394513/100000000000000 : ℝ)^55
        have hw : |(6422070701/10000000000 : ℝ)|=(6422070701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1401839539/5000000000 : ℝ)|^71 ≤ (154937815989/800000000000 : ℝ)^55
        have hw : |(-1401839539/5000000000 : ℝ)|=(1401839539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1664531591/5000000000 : ℝ)|^71 ≤ (24174704595963/100000000000000 : ℝ)^55
        have hw : |(-1664531591/5000000000 : ℝ)|=(1664531591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3805889687/10000000000 : ℝ)*x 0 + (5167626383/10000000000 : ℝ)*x 1 + (3793972011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3805889687/10000000000 : ℝ)^71 ≤ (5746945588409/20000000000000 : ℝ)^55 := by
    have hnat : (3805889687 : ℕ)^71*20000000000000^55 ≤ 5746945588409^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805889687 10000000000 5746945588409 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167626383/10000000000 : ℝ)^71 ≤ (21323323106187/50000000000000 : ℝ)^55 := by
    have hnat : (5167626383 : ℕ)^71*50000000000000^55 ≤ 21323323106187^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167626383 10000000000 21323323106187 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3793972011/10000000000 : ℝ)^71 ≤ (28618625828497/100000000000000 : ℝ)^55 := by
    have hnat : (3793972011 : ℕ)^71*100000000000000^55 ≤ 28618625828497^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3793972011 10000000000 28618625828497 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3805889687/10000000000 : ℝ), (5167626383/10000000000 : ℝ), (3793972011/10000000000 : ℝ)] ![(5746945588409/20000000000000 : ℝ), (21323323106187/50000000000000 : ℝ), (28618625828497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3805889687/10000000000 : ℝ)|^71 ≤ (5746945588409/20000000000000 : ℝ)^55
        have hw : |(3805889687/10000000000 : ℝ)|=(3805889687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167626383/10000000000 : ℝ)|^71 ≤ (21323323106187/50000000000000 : ℝ)^55
        have hw : |(5167626383/10000000000 : ℝ)|=(5167626383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3793972011/10000000000 : ℝ)|^71 ≤ (28618625828497/100000000000000 : ℝ)^55
        have hw : |(3793972011/10000000000 : ℝ)|=(3793972011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310079_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (471944023/1250000000 : ℝ)*x 0 + (4871182573/10000000000 : ℝ)*x 1 + (-517669233/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471944023/1250000000 : ℝ)^71 ≤ (7109847099807/25000000000000 : ℝ)^55 := by
    have hnat : (471944023 : ℕ)^71*25000000000000^55 ≤ 7109847099807^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471944023 1250000000 7109847099807 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871182573/10000000000 : ℝ)^71 ≤ (39515221140023/100000000000000 : ℝ)^55 := by
    have hnat : (4871182573 : ℕ)^71*100000000000000^55 ≤ 39515221140023^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871182573 10000000000 39515221140023 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517669233/1250000000 : ℝ)^71 ≤ (6409078089547/20000000000000 : ℝ)^55 := by
    have hnat : (517669233 : ℕ)^71*20000000000000^55 ≤ 6409078089547^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517669233 1250000000 6409078089547 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471944023/1250000000 : ℝ), (4871182573/10000000000 : ℝ), (-517669233/1250000000 : ℝ)] ![(7109847099807/25000000000000 : ℝ), (39515221140023/100000000000000 : ℝ), (6409078089547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471944023/1250000000 : ℝ)|^71 ≤ (7109847099807/25000000000000 : ℝ)^55
        have hw : |(471944023/1250000000 : ℝ)|=(471944023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871182573/10000000000 : ℝ)|^71 ≤ (39515221140023/100000000000000 : ℝ)^55
        have hw : |(4871182573/10000000000 : ℝ)|=(4871182573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517669233/1250000000 : ℝ)|^71 ≤ (6409078089547/20000000000000 : ℝ)^55
        have hw : |(-517669233/1250000000 : ℝ)|=(517669233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310079 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((8046888769/10000000000 : ℝ)*X 1 0+(-191116071/1250000000 : ℝ)*X 1 1+(-296493013/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1587001963/5000000000 : ℝ)*X 2 0+(2991130797/5000000000 : ℝ)*X 2 1+(3496069181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-69376993/400000000 : ℝ)*X 0 0+(2966011491/10000000000 : ℝ)*X 0 1+(-467568149/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((804253129/1000000000 : ℝ)*X 1 0+(-63038963/2000000000 : ℝ)*X 1 1+(-3241855461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1478201919/10000000000 : ℝ)*X 2 0+(975560109/1250000000 : ℝ)*X 2 1+(1376069407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((477638691/2000000000 : ℝ)*X 0 0+(1893138903/2500000000 : ℝ)*X 0 1+(-2230197063/10000000000 : ℝ)*X 0 2+(477638691/2000000000 : ℝ)*X 1 0+(1893138903/2500000000 : ℝ)*X 1 1+(-2230197063/10000000000 : ℝ)*X 1 2+(477638691/2000000000 : ℝ)*X 2 0+(1893138903/2500000000 : ℝ)*X 2 1+(-2230197063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-317021121/10000000000 : ℝ)*X 0 0+(1788000899/5000000000 : ℝ)*X 0 1+(-243133609/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2294964269/2500000000 : ℝ)*X 1 0+(-253815473/2000000000 : ℝ)*X 1 1+(-744562693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1904702383/5000000000 : ℝ)*X 2 0+(1465628779/2500000000 : ℝ)*X 2 1+(59792177/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((9999999929/10000000000 : ℝ)*X 1 0+(2963/5000000000 : ℝ)*X 1 1+(9999999929/10000000000 : ℝ)*X 2 0+(2963/5000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1303806973/5000000000 : ℝ)*X 0 0+(1640145977/5000000000 : ℝ)*X 0 1+(-6613908387/10000000000 : ℝ)*X 0 2+(1303806973/5000000000 : ℝ)*X 1 0+(1640145977/5000000000 : ℝ)*X 1 1+(-6613908387/10000000000 : ℝ)*X 1 2+(1303806973/5000000000 : ℝ)*X 2 0+(1640145977/5000000000 : ℝ)*X 2 1+(-6613908387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-446044869/10000000000 : ℝ)*X 0 0+(352317347/625000000 : ℝ)*X 0 1+(-5888951913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9579671657/10000000000 : ℝ)*X 1 0+(-178458387/5000000000 : ℝ)*X 1 1+(-208107259/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((515058143/2000000000 : ℝ)*X 2 0+(242240897/400000000 : ℝ)*X 2 1+(1983064617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2092255809/5000000000 : ℝ)*X 0 0+(5416449819/10000000000 : ℝ)*X 0 1+(-3117168187/10000000000 : ℝ)*X 0 2+(2092255809/5000000000 : ℝ)*X 1 0+(5416449819/10000000000 : ℝ)*X 1 1+(-3117168187/10000000000 : ℝ)*X 1 2+(2092255809/5000000000 : ℝ)*X 2 0+(5416449819/10000000000 : ℝ)*X 2 1+(-3117168187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((19807/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19807/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3491010340260458425431/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411783/1000000000000 : ℝ)*(base18) + (200312204009/250000000000 : ℝ)*(base39) + (1029187593449/1000000000000 : ℝ)*(base49) + (3538861/1000000000000 : ℝ)*(base53) + (629145844901/1000000000000 : ℝ)*(base60) + (2667472113839/1000000000000 : ℝ)*(major_s0_0) + (2667472113839/1000000000000 : ℝ)*(major_s0_1) + (1333734287489/500000000000 : ℝ)*(major_s0_2) + (8885761/500000000000 : ℝ)*(sp_s0_1) + (3686227106761/1000000000000 : ℝ)*(sp_s0_7) + (3686226253987/1000000000000 : ℝ)*(sp_s0_8) + (3686247976153/1000000000000 : ℝ)*(sp_s0_9) + (329738877929/200000000000 : ℝ)*(sp_s0_13) + (4332633/250000000000 : ℝ)*(sp_s0_14) + (329738877929/200000000000 : ℝ)*(f.failure) + (3686247976153/1000000000000 : ℝ)*(f.sum) + (40448967791947/2000000000000000000000000000 : ℝ)*base62 + (2625429381943951/5000000000000000000000000000 : ℝ)*base65 + (7141071173642117/10000000000000000000000000000 : ℝ)*base67 + (237729666126933/5000000000000000000000000000 : ℝ)*base69 + (1159738230649157/2000000000000000000000000000 : ℝ)*base71 + (2699206053786399/10000000000000000000000000000 : ℝ)*base72 + (5072186901786399/10000000000000000000000000000 : ℝ)*base75 + (2927544145357883/10000000000000000000000000000 : ℝ)*base77 + (2680257596072141/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (13303/20000000000000000 : ℝ)*base86 + (13303/20000000000000000 : ℝ)*base88 + (13303/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((25421/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(25421/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34821191586736377821397/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599662606897/500000000000 : ℝ)*(base39) + (159003234187/250000000000 : ℝ)*(base49) + (413211277343/500000000000 : ℝ)*(base60) + (1601095383967/500000000000 : ℝ)*(major_s0_0) + (640431753389/200000000000 : ℝ)*(major_s0_1) + (640431753389/200000000000 : ℝ)*(major_s0_2) + (34843173/1000000000000 : ℝ)*(sp_s0_1) + (20835951/500000000000 : ℝ)*(sp_s0_7) + (4425101065349/1000000000000 : ℝ)*(sp_s0_14) + (2212500620927/500000000000 : ℝ)*(sp_s0_15) + (4425142737251/1000000000000 : ℝ)*(sp_s0_16) + (3200099/100000000000 : ℝ)*(sp_s0_17) + (494792538451/250000000000 : ℝ)*(sp_s0_20) + (106652223/1000000000000 : ℝ)*(sp_s0_22) + (494792538451/250000000000 : ℝ)*(f.failure) + (4425142737251/1000000000000 : ℝ)*(f.sum) + (430942427036409/1000000000000000000000000000 : ℝ)*base62 + (861156535442051/2000000000000000000000000000 : ℝ)*base65 + (525822436769233/2000000000000000000000000000 : ℝ)*base66 + (344196946830767/2000000000000000000000000000 : ℝ)*base68 + (721767585642853/10000000000000000000000000000 : ℝ)*base71 + (5674760263549647/5000000000000000000000000000 : ℝ)*base72 + (2536243527442051/2000000000000000000000000000 : ℝ)*base74 + (455296408216299/5000000000000000000000000000 : ℝ)*base77 + (9094215730945459/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (2643/25000000000000000 : ℝ)*base87 + (22357/25000000000000000 : ℝ)*base88 + (22357/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8043/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8043/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20192240537510603548701/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125767374587/125000000000 : ℝ)*(base39) + (132279512921/200000000000 : ℝ)*(base49) + (2227027/1000000000000 : ℝ)*(base50) + (2434288554693/1000000000000 : ℝ)*(major_s0_0) + (2434288554693/1000000000000 : ℝ)*(major_s0_1) + (2434288554693/1000000000000 : ℝ)*(major_s0_2) + (98763281/1000000000000 : ℝ)*(sp_s0_2) + (1195383/250000000000 : ℝ)*(sp_s0_9) + (864947/125000000000 : ℝ)*(sp_s0_13) + (8791451/500000000000 : ℝ)*(sp_s0_15) + (3364004655293/1000000000000 : ℝ)*(sp_s0_21) + (336398707239/100000000000 : ℝ)*(sp_s0_22) + (42048763881/12500000000 : ℝ)*(sp_s0_23) + (752281421107/500000000000 : ℝ)*(sp_s0_27) + (150456976179/100000000000 : ℝ)*(f.failure) + (3364004655293/1000000000000 : ℝ)*(f.sum) + (1928976695400433/5000000000000000000000000000 : ℝ)*base62 + (123185018795413/10000000000000000000000000000 : ℝ)*base64 + (2425236995596279/10000000000000000000000000000 : ℝ)*base67 + (8116557705403721/10000000000000000000000000000 : ℝ)*base69 + (81469843347923/2500000000000000000000000000 : ℝ)*base70 + (2550059927204587/10000000000000000000000000000 : ℝ)*base73 + (4210829141204587/10000000000000000000000000000 : ℝ)*base74 + (690120223403721/10000000000000000000000000000 : ℝ)*base77 + (2525915376400433/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1053/10000000000000000 : ℝ)*base86 + (1053/10000000000000000 : ℝ)*base88 + (1053/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (19807/50000 : ℝ) ^ (35/8 : ℝ) ≤ (174015546773172073/10000000000000000000 : ℝ) := by
    have hpowers : (19807/50000 : ℝ)^35 ≤ (174015546773172073/10000000000000000000 : ℝ)^8 := by
      have hnat : (19807 : ℕ)^35*10000000000000000000^8 ≤ 174015546773172073^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19807 50000 174015546773172073 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19807/50000 : ℝ)) (X := (174015546773172073/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10174015546773172073/10000000000000000000 : ℝ) ≤ (10039510721850283/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10174015546773172073/10000000000000000000 : ℝ)^8 ≤ (10039510721850283/10000000000000000 : ℝ)^35 := by
      have hnat : (10174015546773172073 : ℕ)^8*10000000000000000^35 ≤ 10039510721850283^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10174015546773172073 10000000000000000000 10039510721850283 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10039510721850283/10000000000000000 : ℝ)) (X := (10174015546773172073/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5174015546773172073/5000000000000000000 : ℝ) ≤ (10078503510797499/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5174015546773172073/5000000000000000000 : ℝ)^8 ≤ (10078503510797499/10000000000000000 : ℝ)^35 := by
      have hnat : (5174015546773172073 : ℕ)^8*10000000000000000^35 ≤ 10078503510797499^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5174015546773172073 5000000000000000000 10078503510797499 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10078503510797499/10000000000000000 : ℝ)) (X := (5174015546773172073/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(39510721850283/3961400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2437049309201/247587500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (19807/50000 : ℝ)) (alpha := (39510721850283/3961400000000000 : ℝ)) (beta := (2437049309201/247587500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19807/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(39510721850283/3961400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2437049309201/247587500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (25421/50000 : ℝ) ^ (35/8 : ℝ) ≤ (5184704273947327227/100000000000000000000 : ℝ) := by
    have hpowers : (25421/50000 : ℝ)^35 ≤ (5184704273947327227/100000000000000000000 : ℝ)^8 := by
      have hnat : (25421 : ℕ)^35*100000000000000000000^8 ≤ 5184704273947327227^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25421 50000 5184704273947327227 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25421/50000 : ℝ)) (X := (5184704273947327227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105184704273947327227/100000000000000000000 : ℝ) ≤ (10116207641237329/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (105184704273947327227/100000000000000000000 : ℝ)^8 ≤ (10116207641237329/10000000000000000 : ℝ)^35 := by
      have hnat : (105184704273947327227 : ℕ)^8*10000000000000000^35 ≤ 10116207641237329^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105184704273947327227 100000000000000000000 10116207641237329 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10116207641237329/10000000000000000 : ℝ)) (X := (105184704273947327227/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55184704273947327227/50000000000000000000 : ℝ) ≤ (10228077075149359/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (55184704273947327227/50000000000000000000 : ℝ)^8 ≤ (10228077075149359/10000000000000000 : ℝ)^35 := by
      have hnat : (55184704273947327227 : ℕ)^8*10000000000000000^35 ≤ 10228077075149359^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55184704273947327227 50000000000000000000 10228077075149359 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10228077075149359/10000000000000000 : ℝ)) (X := (55184704273947327227/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(116207641237329/5084200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(11186943391203/508420000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (25421/50000 : ℝ)) (alpha := (116207641237329/5084200000000000 : ℝ)) (beta := (11186943391203/508420000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (25421/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(116207641237329/5084200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(11186943391203/508420000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8043/20000 : ℝ) ^ (35/8 : ℝ) ≤ (92932543548120081/5000000000000000000 : ℝ) := by
    have hpowers : (8043/20000 : ℝ)^35 ≤ (92932543548120081/5000000000000000000 : ℝ)^8 := by
      have hnat : (8043 : ℕ)^35*5000000000000000000^8 ≤ 92932543548120081^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8043 20000 92932543548120081 5000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8043/20000 : ℝ)) (X := (92932543548120081/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5092932543548120081/5000000000000000000 : ℝ) ≤ (80337457450391/80000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5092932543548120081/5000000000000000000 : ℝ)^8 ≤ (80337457450391/80000000000000 : ℝ)^35 := by
      have hnat : (5092932543548120081 : ℕ)^8*80000000000000^35 ≤ 80337457450391^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5092932543548120081 5000000000000000000 80337457450391 80000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80337457450391/80000000000000 : ℝ)) (X := (5092932543548120081/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2592932543548120081/2500000000000000000 : ℝ) ≤ (252094367461137/250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2592932543548120081/2500000000000000000 : ℝ)^8 ≤ (252094367461137/250000000000000 : ℝ)^35 := by
      have hnat : (2592932543548120081 : ℕ)^8*250000000000000^35 ≤ 252094367461137^35*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2592932543548120081 2500000000000000000 252094367461137 250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252094367461137/250000000000000 : ℝ)) (X := (2592932543548120081/2500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(112485816797/10724000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8318503429321/804300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (8043/20000 : ℝ)) (alpha := (112485816797/10724000000000 : ℝ)) (beta := (8318503429321/804300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8043/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(112485816797/10724000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8318503429321/804300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1325126329/5000000000 : ℝ)*X 0 0+(4413266151/10000000000 : ℝ)*X 0 1+(-5590364347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6422070701/10000000000 : ℝ)*X 1 0+(-1401839539/5000000000 : ℝ)*X 1 1+(-1664531591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3805889687/10000000000 : ℝ)*X 2 0+(5167626383/10000000000 : ℝ)*X 2 1+(3793972011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((471944023/1250000000 : ℝ)*X 0 0+(4871182573/10000000000 : ℝ)*X 0 1+(-517669233/1250000000 : ℝ)*X 0 2+(471944023/1250000000 : ℝ)*X 1 0+(4871182573/10000000000 : ℝ)*X 1 1+(-517669233/1250000000 : ℝ)*X 1 2+(471944023/1250000000 : ℝ)*X 2 0+(4871182573/10000000000 : ℝ)*X 2 1+(-517669233/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-88395410545484733664933618377/13275641750000000000000000000 : ℝ) := by norm_num
    linear_combination (24279/1000000000000 : ℝ)*(base16) + (411/1000000000000 : ℝ)*(base18) + (4753/500000000000 : ℝ)*(base23) + (448987237437/1000000000000 : ℝ)*(base39) + (1773/62500000000 : ℝ)*(base43) + (3359/250000000000 : ℝ)*(base44) + (360062006007/1000000000000 : ℝ)*(base49) + (84012893753/500000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s1_0) + (404482489549/250000000000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2219488671563/1000000000000 : ℝ)*(sp_s1_0) + (443897732361/200000000000 : ℝ)*(sp_s1_1) + (2219488662057/1000000000000 : ℝ)*(sp_s1_2) + (249999996641/250000000000 : ℝ)*(sp_s1_6) + (2219488699931/1000000000000 : ℝ)*(f.sum) + (58249033838939/665563486328125000000000000 : ℝ)*base62 + (4038602510203/5362000000000000000000000 : ℝ)*base65 + (17296928317091/317762500000000000000000000 : ℝ)*base67 + (7067015428161/26810000000000000000000000 : ℝ)*base68 + (66404846780854203/265512835000000000000000000000 : ℝ)*base71 + (47134568356779/99035000000000000000000000 : ℝ)*base72 + (91448922175471/254210000000000000000000000 : ℝ)*base75 + (24036362847579/198070000000000000000000000 : ℝ)*base77 + (373178237319192951/786740229687500000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b035 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c310079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
