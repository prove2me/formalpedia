-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:51.71172+00:00
-- url     : https://prove2.me/submissions/3ef470c0-5659-41b9-b103-342dfdafc28b

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314031_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314031 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c314031_s0 p hpa hpb X hX
  have h1 := collision_c314031_s1 p hpa hpb X hX h0
  exact collision_c314031_s2 p hpa hpb X hX h1

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
theorem collision_support_c314030_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-291552539/1000000000 : ℝ)*x 0 + (1194159339/2500000000 : ℝ)*x 1 + (-1207677579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291552539/1000000000 : ℝ)^19 ≤ (10494086821187/50000000000000 : ℝ)^15 := by
    have hnat : (291552539 : ℕ)^19*50000000000000^15 ≤ 10494086821187^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291552539 1000000000 10494086821187 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194159339/2500000000 : ℝ)^19 ≤ (19612135296429/50000000000000 : ℝ)^15 := by
    have hnat : (1194159339 : ℕ)^19*50000000000000^15 ≤ 19612135296429^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194159339 2500000000 19612135296429 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207677579/2500000000 : ℝ)^19 ≤ (4973444468693/12500000000000 : ℝ)^15 := by
    have hnat : (1207677579 : ℕ)^19*12500000000000^15 ≤ 4973444468693^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207677579 2500000000 4973444468693 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291552539/1000000000 : ℝ), (1194159339/2500000000 : ℝ), (-1207677579/2500000000 : ℝ)] ![(10494086821187/50000000000000 : ℝ), (19612135296429/50000000000000 : ℝ), (4973444468693/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291552539/1000000000 : ℝ)|^19 ≤ (10494086821187/50000000000000 : ℝ)^15
        have hw : |(-291552539/1000000000 : ℝ)|=(291552539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194159339/2500000000 : ℝ)|^19 ≤ (19612135296429/50000000000000 : ℝ)^15
        have hw : |(1194159339/2500000000 : ℝ)|=(1194159339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1207677579/2500000000 : ℝ)|^19 ≤ (4973444468693/12500000000000 : ℝ)^15
        have hw : |(-1207677579/2500000000 : ℝ)|=(1207677579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6950906739/10000000000 : ℝ)*x 0 + (-217670233/2000000000 : ℝ)*x 1 + (-494485401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6950906739/10000000000 : ℝ)^19 ≤ (31541997210937/50000000000000 : ℝ)^15 := by
    have hnat : (6950906739 : ℕ)^19*50000000000000^15 ≤ 31541997210937^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6950906739 10000000000 31541997210937 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217670233/2000000000 : ℝ)^19 ≤ (753039005069/12500000000000 : ℝ)^15 := by
    have hnat : (217670233 : ℕ)^19*12500000000000^15 ≤ 753039005069^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217670233 2000000000 753039005069 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494485401/1250000000 : ℝ)^19 ≤ (3089169351837/10000000000000 : ℝ)^15 := by
    have hnat : (494485401 : ℕ)^19*10000000000000^15 ≤ 3089169351837^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494485401 1250000000 3089169351837 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6950906739/10000000000 : ℝ), (-217670233/2000000000 : ℝ), (-494485401/1250000000 : ℝ)] ![(31541997210937/50000000000000 : ℝ), (753039005069/12500000000000 : ℝ), (3089169351837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6950906739/10000000000 : ℝ)|^19 ≤ (31541997210937/50000000000000 : ℝ)^15
        have hw : |(6950906739/10000000000 : ℝ)|=(6950906739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217670233/2000000000 : ℝ)|^19 ≤ (753039005069/12500000000000 : ℝ)^15
        have hw : |(-217670233/2000000000 : ℝ)|=(217670233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494485401/1250000000 : ℝ)|^19 ≤ (3089169351837/10000000000000 : ℝ)^15
        have hw : |(-494485401/1250000000 : ℝ)|=(494485401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2627013223/10000000000 : ℝ)*x 0 + (5485573301/10000000000 : ℝ)*x 1 + (1088169213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627013223/10000000000 : ℝ)^19 ≤ (18392984060383/100000000000000 : ℝ)^15 := by
    have hnat : (2627013223 : ℕ)^19*100000000000000^15 ≤ 18392984060383^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627013223 10000000000 18392984060383 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485573301/10000000000 : ℝ)^19 ≤ (46739195062479/100000000000000 : ℝ)^15 := by
    have hnat : (5485573301 : ℕ)^19*100000000000000^15 ≤ 46739195062479^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485573301 10000000000 46739195062479 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088169213/2500000000 : ℝ)^19 ≤ (1089619401803/3125000000000 : ℝ)^15 := by
    have hnat : (1088169213 : ℕ)^19*3125000000000^15 ≤ 1089619401803^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088169213 2500000000 1089619401803 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627013223/10000000000 : ℝ), (5485573301/10000000000 : ℝ), (1088169213/2500000000 : ℝ)] ![(18392984060383/100000000000000 : ℝ), (46739195062479/100000000000000 : ℝ), (1089619401803/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627013223/10000000000 : ℝ)|^19 ≤ (18392984060383/100000000000000 : ℝ)^15
        have hw : |(2627013223/10000000000 : ℝ)|=(2627013223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485573301/10000000000 : ℝ)|^19 ≤ (46739195062479/100000000000000 : ℝ)^15
        have hw : |(5485573301/10000000000 : ℝ)|=(5485573301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088169213/2500000000 : ℝ)|^19 ≤ (1089619401803/3125000000000 : ℝ)^15
        have hw : |(1088169213/2500000000 : ℝ)|=(1088169213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_4 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^19 ≤ (1 : ℝ)^15 := by
    have hnat : (1 : ℕ)^19*1^15 ≤ 1^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^19 ≤ (1 : ℝ)^15
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1843191567/5000000000 : ℝ)*x 0 + (3248642597/5000000000 : ℝ)*x 1 + (-2097985441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843191567/5000000000 : ℝ)^19 ≤ (28250573103481/100000000000000 : ℝ)^15 := by
    have hnat : (1843191567 : ℕ)^19*100000000000000^15 ≤ 28250573103481^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843191567 5000000000 28250573103481 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3248642597/5000000000 : ℝ)^19 ≤ (2895768120477/5000000000000 : ℝ)^15 := by
    have hnat : (3248642597 : ℕ)^19*5000000000000^15 ≤ 2895768120477^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248642597 5000000000 2895768120477 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097985441/10000000000 : ℝ)^19 ≤ (3458516118827/25000000000000 : ℝ)^15 := by
    have hnat : (2097985441 : ℕ)^19*25000000000000^15 ≤ 3458516118827^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097985441 10000000000 3458516118827 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1843191567/5000000000 : ℝ), (3248642597/5000000000 : ℝ), (-2097985441/10000000000 : ℝ)] ![(28250573103481/100000000000000 : ℝ), (2895768120477/5000000000000 : ℝ), (3458516118827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1843191567/5000000000 : ℝ)|^19 ≤ (28250573103481/100000000000000 : ℝ)^15
        have hw : |(1843191567/5000000000 : ℝ)|=(1843191567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3248642597/5000000000 : ℝ)|^19 ≤ (2895768120477/5000000000000 : ℝ)^15
        have hw : |(3248642597/5000000000 : ℝ)|=(3248642597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097985441/10000000000 : ℝ)|^19 ≤ (3458516118827/25000000000000 : ℝ)^15
        have hw : |(-2097985441/10000000000 : ℝ)|=(2097985441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-172830353/625000000 : ℝ)*x 0 + (3816966787/10000000000 : ℝ)*x 1 + (-234515707/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172830353/625000000 : ℝ)^19 ≤ (19627756711311/100000000000000 : ℝ)^15 := by
    have hnat : (172830353 : ℕ)^19*100000000000000^15 ≤ 19627756711311^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172830353 625000000 19627756711311 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3816966787/10000000000 : ℝ)^19 ≤ (1476204824201/5000000000000 : ℝ)^15 := by
    have hnat : (3816966787 : ℕ)^19*5000000000000^15 ≤ 1476204824201^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3816966787 10000000000 1476204824201 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234515707/400000000 : ℝ)^19 ≤ (50848146788459/100000000000000 : ℝ)^15 := by
    have hnat : (234515707 : ℕ)^19*100000000000000^15 ≤ 50848146788459^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234515707 400000000 50848146788459 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172830353/625000000 : ℝ), (3816966787/10000000000 : ℝ), (-234515707/400000000 : ℝ)] ![(19627756711311/100000000000000 : ℝ), (1476204824201/5000000000000 : ℝ), (50848146788459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172830353/625000000 : ℝ)|^19 ≤ (19627756711311/100000000000000 : ℝ)^15
        have hw : |(-172830353/625000000 : ℝ)|=(172830353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3816966787/10000000000 : ℝ)|^19 ≤ (1476204824201/5000000000000 : ℝ)^15
        have hw : |(3816966787/10000000000 : ℝ)|=(3816966787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234515707/400000000 : ℝ)|^19 ≤ (50848146788459/100000000000000 : ℝ)^15
        have hw : |(-234515707/400000000 : ℝ)|=(234515707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1834831429/2500000000 : ℝ)*x 0 + (-92146857/2500000000 : ℝ)*x 1 + (-3955653061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834831429/2500000000 : ℝ)^19 ≤ (67582015317777/100000000000000 : ℝ)^15 := by
    have hnat : (1834831429 : ℕ)^19*100000000000000^15 ≤ 67582015317777^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834831429 2500000000 67582015317777 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92146857/2500000000 : ℝ)^19 ≤ (1528567621749/100000000000000 : ℝ)^15 := by
    have hnat : (92146857 : ℕ)^19*100000000000000^15 ≤ 1528567621749^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92146857 2500000000 1528567621749 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3955653061/10000000000 : ℝ)^19 ≤ (30889417045141/100000000000000 : ℝ)^15 := by
    have hnat : (3955653061 : ℕ)^19*100000000000000^15 ≤ 30889417045141^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955653061 10000000000 30889417045141 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1834831429/2500000000 : ℝ), (-92146857/2500000000 : ℝ), (-3955653061/10000000000 : ℝ)] ![(67582015317777/100000000000000 : ℝ), (1528567621749/100000000000000 : ℝ), (30889417045141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1834831429/2500000000 : ℝ)|^19 ≤ (67582015317777/100000000000000 : ℝ)^15
        have hw : |(1834831429/2500000000 : ℝ)|=(1834831429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92146857/2500000000 : ℝ)|^19 ≤ (1528567621749/100000000000000 : ℝ)^15
        have hw : |(-92146857/2500000000 : ℝ)|=(92146857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3955653061/10000000000 : ℝ)|^19 ≤ (30889417045141/100000000000000 : ℝ)^15
        have hw : |(-3955653061/10000000000 : ℝ)|=(3955653061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1725750321/10000000000 : ℝ)*x 0 + (848465309/1250000000 : ℝ)*x 1 + (365889467/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725750321/10000000000 : ℝ)^19 ≤ (5401015503743/50000000000000 : ℝ)^15 := by
    have hnat : (1725750321 : ℕ)^19*50000000000000^15 ≤ 5401015503743^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725750321 10000000000 5401015503743 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848465309/1250000000 : ℝ)^19 ≤ (61213963138901/100000000000000 : ℝ)^15 := by
    have hnat : (848465309 : ℕ)^19*100000000000000^15 ≤ 61213963138901^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848465309 1250000000 61213963138901 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365889467/1000000000 : ℝ)^19 ≤ (13992002920693/50000000000000 : ℝ)^15 := by
    have hnat : (365889467 : ℕ)^19*50000000000000^15 ≤ 13992002920693^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365889467 1000000000 13992002920693 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1725750321/10000000000 : ℝ), (848465309/1250000000 : ℝ), (365889467/1000000000 : ℝ)] ![(5401015503743/50000000000000 : ℝ), (61213963138901/100000000000000 : ℝ), (13992002920693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1725750321/10000000000 : ℝ)|^19 ≤ (5401015503743/50000000000000 : ℝ)^15
        have hw : |(1725750321/10000000000 : ℝ)|=(1725750321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848465309/1250000000 : ℝ)|^19 ≤ (61213963138901/100000000000000 : ℝ)^15
        have hw : |(848465309/1250000000 : ℝ)|=(848465309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365889467/1000000000 : ℝ)|^19 ≤ (13992002920693/50000000000000 : ℝ)^15
        have hw : |(365889467/1000000000 : ℝ)|=(365889467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_12 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2802114427/10000000000 : ℝ)*x 0 + (1905965379/2500000000 : ℝ)*x 1 + (-1510246709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2802114427/10000000000 : ℝ)^19 ≤ (498986472923/2500000000000 : ℝ)^15 := by
    have hnat : (2802114427 : ℕ)^19*2500000000000^15 ≤ 498986472923^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802114427 10000000000 498986472923 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905965379/2500000000 : ℝ)^19 ≤ (70917758217587/100000000000000 : ℝ)^15 := by
    have hnat : (1905965379 : ℕ)^19*100000000000000^15 ≤ 70917758217587^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905965379 2500000000 70917758217587 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510246709/10000000000 : ℝ)^19 ≤ (2280695712723/25000000000000 : ℝ)^15 := by
    have hnat : (1510246709 : ℕ)^19*25000000000000^15 ≤ 2280695712723^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510246709 10000000000 2280695712723 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2802114427/10000000000 : ℝ), (1905965379/2500000000 : ℝ), (-1510246709/10000000000 : ℝ)] ![(498986472923/2500000000000 : ℝ), (70917758217587/100000000000000 : ℝ), (2280695712723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2802114427/10000000000 : ℝ)|^19 ≤ (498986472923/2500000000000 : ℝ)^15
        have hw : |(2802114427/10000000000 : ℝ)|=(2802114427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1905965379/2500000000 : ℝ)|^19 ≤ (70917758217587/100000000000000 : ℝ)^15
        have hw : |(1905965379/2500000000 : ℝ)|=(1905965379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1510246709/10000000000 : ℝ)|^19 ≤ (2280695712723/25000000000000 : ℝ)^15
        have hw : |(-1510246709/10000000000 : ℝ)|=(1510246709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3444466539/10000000000 : ℝ)*x 0 + (184429223/400000000 : ℝ)*x 1 + (-282475287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3444466539/10000000000 : ℝ)^19 ≤ (25923153346893/100000000000000 : ℝ)^15 := by
    have hnat : (3444466539 : ℕ)^19*100000000000000^15 ≤ 25923153346893^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3444466539 10000000000 25923153346893 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184429223/400000000 : ℝ)^19 ≤ (37506655889421/100000000000000 : ℝ)^15 := by
    have hnat : (184429223 : ℕ)^19*100000000000000^15 ≤ 37506655889421^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184429223 400000000 37506655889421 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282475287/625000000 : ℝ)^19 ≤ (7314038148741/20000000000000 : ℝ)^15 := by
    have hnat : (282475287 : ℕ)^19*20000000000000^15 ≤ 7314038148741^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282475287 625000000 7314038148741 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3444466539/10000000000 : ℝ), (184429223/400000000 : ℝ), (-282475287/625000000 : ℝ)] ![(25923153346893/100000000000000 : ℝ), (37506655889421/100000000000000 : ℝ), (7314038148741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3444466539/10000000000 : ℝ)|^19 ≤ (25923153346893/100000000000000 : ℝ)^15
        have hw : |(-3444466539/10000000000 : ℝ)|=(3444466539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184429223/400000000 : ℝ)|^19 ≤ (37506655889421/100000000000000 : ℝ)^15
        have hw : |(184429223/400000000 : ℝ)|=(184429223/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282475287/625000000 : ℝ)|^19 ≤ (7314038148741/20000000000000 : ℝ)^15
        have hw : |(-282475287/625000000 : ℝ)|=(282475287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1800322211/2500000000 : ℝ)*x 0 + (-1139020453/10000000000 : ℝ)*x 1 + (-3623566829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800322211/2500000000 : ℝ)^19 ≤ (13195209444357/20000000000000 : ℝ)^15 := by
    have hnat : (1800322211 : ℕ)^19*20000000000000^15 ≤ 13195209444357^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800322211 2500000000 13195209444357 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139020453/10000000000 : ℝ)^19 ≤ (1276350416183/20000000000000 : ℝ)^15 := by
    have hnat : (1139020453 : ℕ)^19*20000000000000^15 ≤ 1276350416183^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139020453 10000000000 1276350416183 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3623566829/10000000000 : ℝ)^19 ≤ (6910550168059/25000000000000 : ℝ)^15 := by
    have hnat : (3623566829 : ℕ)^19*25000000000000^15 ≤ 6910550168059^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623566829 10000000000 6910550168059 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1800322211/2500000000 : ℝ), (-1139020453/10000000000 : ℝ), (-3623566829/10000000000 : ℝ)] ![(13195209444357/20000000000000 : ℝ), (1276350416183/20000000000000 : ℝ), (6910550168059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1800322211/2500000000 : ℝ)|^19 ≤ (13195209444357/20000000000000 : ℝ)^15
        have hw : |(1800322211/2500000000 : ℝ)|=(1800322211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139020453/10000000000 : ℝ)|^19 ≤ (1276350416183/20000000000000 : ℝ)^15
        have hw : |(-1139020453/10000000000 : ℝ)|=(1139020453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3623566829/10000000000 : ℝ)|^19 ≤ (6910550168059/25000000000000 : ℝ)^15
        have hw : |(-3623566829/10000000000 : ℝ)|=(3623566829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (17003817/80000000 : ℝ)*x 0 + (26693083/50000000 : ℝ)*x 1 + (2462654549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17003817/80000000 : ℝ)^19 ≤ (14064085072373/100000000000000 : ℝ)^15 := by
    have hnat : (17003817 : ℕ)^19*100000000000000^15 ≤ 14064085072373^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17003817 80000000 14064085072373 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26693083/50000000 : ℝ)^19 ≤ (11289717371749/25000000000000 : ℝ)^15 := by
    have hnat : (26693083 : ℕ)^19*25000000000000^15 ≤ 11289717371749^15*50000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26693083 50000000 11289717371749 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462654549/5000000000 : ℝ)^19 ≤ (10194261355149/25000000000000 : ℝ)^15 := by
    have hnat : (2462654549 : ℕ)^19*25000000000000^15 ≤ 10194261355149^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462654549 5000000000 10194261355149 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17003817/80000000 : ℝ), (26693083/50000000 : ℝ), (2462654549/5000000000 : ℝ)] ![(14064085072373/100000000000000 : ℝ), (11289717371749/25000000000000 : ℝ), (10194261355149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17003817/80000000 : ℝ)|^19 ≤ (14064085072373/100000000000000 : ℝ)^15
        have hw : |(17003817/80000000 : ℝ)|=(17003817/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26693083/50000000 : ℝ)|^19 ≤ (11289717371749/25000000000000 : ℝ)^15
        have hw : |(26693083/50000000 : ℝ)|=(26693083/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462654549/5000000000 : ℝ)|^19 ≤ (10194261355149/25000000000000 : ℝ)^15
        have hw : |(2462654549/5000000000 : ℝ)|=(2462654549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1617184207/5000000000 : ℝ)*x 0 + (6567855407/10000000000 : ℝ)*x 1 + (-627168469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1617184207/5000000000 : ℝ)^19 ≤ (191494661287/800000000000 : ℝ)^15 := by
    have hnat : (1617184207 : ℕ)^19*800000000000^15 ≤ 191494661287^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617184207 5000000000 191494661287 800000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6567855407/10000000000 : ℝ)^19 ≤ (58713306473719/100000000000000 : ℝ)^15 := by
    have hnat : (6567855407 : ℕ)^19*100000000000000^15 ≤ 58713306473719^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6567855407 10000000000 58713306473719 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627168469/2500000000 : ℝ)^19 ≤ (4337465211993/25000000000000 : ℝ)^15 := by
    have hnat : (627168469 : ℕ)^19*25000000000000^15 ≤ 4337465211993^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627168469 2500000000 4337465211993 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1617184207/5000000000 : ℝ), (6567855407/10000000000 : ℝ), (-627168469/2500000000 : ℝ)] ![(191494661287/800000000000 : ℝ), (58713306473719/100000000000000 : ℝ), (4337465211993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1617184207/5000000000 : ℝ)|^19 ≤ (191494661287/800000000000 : ℝ)^15
        have hw : |(1617184207/5000000000 : ℝ)|=(1617184207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6567855407/10000000000 : ℝ)|^19 ≤ (58713306473719/100000000000000 : ℝ)^15
        have hw : |(6567855407/10000000000 : ℝ)|=(6567855407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-627168469/2500000000 : ℝ)|^19 ≤ (4337465211993/25000000000000 : ℝ)^15
        have hw : |(-627168469/2500000000 : ℝ)|=(627168469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033360299/5000000000 : ℝ)*x 0 + (2672703629/5000000000 : ℝ)*x 1 + (-4965112779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033360299/5000000000 : ℝ)^19 ≤ (6786724872741/50000000000000 : ℝ)^15 := by
    have hnat : (1033360299 : ℕ)^19*50000000000000^15 ≤ 6786724872741^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033360299 5000000000 6786724872741 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2672703629/5000000000 : ℝ)^19 ≤ (45231641125859/100000000000000 : ℝ)^15 := by
    have hnat : (2672703629 : ℕ)^19*100000000000000^15 ≤ 45231641125859^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672703629 5000000000 45231641125859 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4965112779/10000000000 : ℝ)^19 ≤ (20597454555421/50000000000000 : ℝ)^15 := by
    have hnat : (4965112779 : ℕ)^19*50000000000000^15 ≤ 20597454555421^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965112779 10000000000 20597454555421 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033360299/5000000000 : ℝ), (2672703629/5000000000 : ℝ), (-4965112779/10000000000 : ℝ)] ![(6786724872741/50000000000000 : ℝ), (45231641125859/100000000000000 : ℝ), (20597454555421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033360299/5000000000 : ℝ)|^19 ≤ (6786724872741/50000000000000 : ℝ)^15
        have hw : |(-1033360299/5000000000 : ℝ)|=(1033360299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2672703629/5000000000 : ℝ)|^19 ≤ (45231641125859/100000000000000 : ℝ)^15
        have hw : |(2672703629/5000000000 : ℝ)|=(2672703629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4965112779/10000000000 : ℝ)|^19 ≤ (20597454555421/50000000000000 : ℝ)^15
        have hw : |(-4965112779/10000000000 : ℝ)|=(4965112779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1022469973/1250000000 : ℝ)*x 0 + (-140768311/2500000000 : ℝ)*x 1 + (-1395279447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022469973/1250000000 : ℝ)^19 ≤ (38765140960219/50000000000000 : ℝ)^15 := by
    have hnat : (1022469973 : ℕ)^19*50000000000000^15 ≤ 38765140960219^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022469973 1250000000 38765140960219 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140768311/2500000000 : ℝ)^19 ≤ (2614461166047/100000000000000 : ℝ)^15 := by
    have hnat : (140768311 : ℕ)^19*100000000000000^15 ≤ 2614461166047^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140768311 2500000000 2614461166047 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395279447/5000000000 : ℝ)^19 ≤ (19855256901567/100000000000000 : ℝ)^15 := by
    have hnat : (1395279447 : ℕ)^19*100000000000000^15 ≤ 19855256901567^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395279447 5000000000 19855256901567 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1022469973/1250000000 : ℝ), (-140768311/2500000000 : ℝ), (-1395279447/5000000000 : ℝ)] ![(38765140960219/50000000000000 : ℝ), (2614461166047/100000000000000 : ℝ), (19855256901567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1022469973/1250000000 : ℝ)|^19 ≤ (38765140960219/50000000000000 : ℝ)^15
        have hw : |(1022469973/1250000000 : ℝ)|=(1022469973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140768311/2500000000 : ℝ)|^19 ≤ (2614461166047/100000000000000 : ℝ)^15
        have hw : |(-140768311/2500000000 : ℝ)|=(140768311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1395279447/5000000000 : ℝ)|^19 ≤ (19855256901567/100000000000000 : ℝ)^15
        have hw : |(-1395279447/5000000000 : ℝ)|=(1395279447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1940160451/10000000000 : ℝ)*x 0 + (5734759363/10000000000 : ℝ)*x 1 + (233053163/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940160451/10000000000 : ℝ)^19 ≤ (12529325352913/100000000000000 : ℝ)^15 := by
    have hnat : (1940160451 : ℕ)^19*100000000000000^15 ≤ 12529325352913^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940160451 10000000000 12529325352913 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5734759363/10000000000 : ℝ)^19 ≤ (24722321880553/50000000000000 : ℝ)^15 := by
    have hnat : (5734759363 : ℕ)^19*50000000000000^15 ≤ 24722321880553^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5734759363 10000000000 24722321880553 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233053163/500000000 : ℝ)^19 ≤ (38026030874581/100000000000000 : ℝ)^15 := by
    have hnat : (233053163 : ℕ)^19*100000000000000^15 ≤ 38026030874581^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233053163 500000000 38026030874581 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1940160451/10000000000 : ℝ), (5734759363/10000000000 : ℝ), (233053163/500000000 : ℝ)] ![(12529325352913/100000000000000 : ℝ), (24722321880553/50000000000000 : ℝ), (38026030874581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1940160451/10000000000 : ℝ)|^19 ≤ (12529325352913/100000000000000 : ℝ)^15
        have hw : |(1940160451/10000000000 : ℝ)|=(1940160451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5734759363/10000000000 : ℝ)|^19 ≤ (24722321880553/50000000000000 : ℝ)^15
        have hw : |(5734759363/10000000000 : ℝ)|=(5734759363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233053163/500000000 : ℝ)|^19 ≤ (38026030874581/100000000000000 : ℝ)^15
        have hw : |(233053163/500000000 : ℝ)|=(233053163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s0_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1165393689/2500000000 : ℝ)*x 0 + (1497058009/2500000000 : ℝ)*x 1 + (-318063103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1165393689/2500000000 : ℝ)^19 ≤ (38031316628461/100000000000000 : ℝ)^15 := by
    have hnat : (1165393689 : ℕ)^19*100000000000000^15 ≤ 38031316628461^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165393689 2500000000 38031316628461 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497058009/2500000000 : ℝ)^19 ≤ (26114492485517/50000000000000 : ℝ)^15 := by
    have hnat : (1497058009 : ℕ)^19*50000000000000^15 ≤ 26114492485517^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497058009 2500000000 26114492485517 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318063103/2000000000 : ℝ)^19 ≤ (973969838773/10000000000000 : ℝ)^15 := by
    have hnat : (318063103 : ℕ)^19*10000000000000^15 ≤ 973969838773^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318063103 2000000000 973969838773 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1165393689/2500000000 : ℝ), (1497058009/2500000000 : ℝ), (-318063103/2000000000 : ℝ)] ![(38031316628461/100000000000000 : ℝ), (26114492485517/50000000000000 : ℝ), (973969838773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1165393689/2500000000 : ℝ)|^19 ≤ (38031316628461/100000000000000 : ℝ)^15
        have hw : |(1165393689/2500000000 : ℝ)|=(1165393689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1497058009/2500000000 : ℝ)|^19 ≤ (26114492485517/50000000000000 : ℝ)^15
        have hw : |(1497058009/2500000000 : ℝ)|=(1497058009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318063103/2000000000 : ℝ)|^19 ≤ (973969838773/10000000000000 : ℝ)^15
        have hw : |(-318063103/2000000000 : ℝ)|=(318063103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748213747/5000000000 : ℝ)*x 0 + (2313406777/5000000000 : ℝ)*x 1 + (-4454877439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748213747/5000000000 : ℝ)^19 ≤ (825609006671/3125000000000 : ℝ)^15 := by
    have hnat : (1748213747 : ℕ)^19*3125000000000^15 ≤ 825609006671^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748213747 5000000000 825609006671 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313406777/5000000000 : ℝ)^19 ≤ (37672450039213/100000000000000 : ℝ)^15 := by
    have hnat : (2313406777 : ℕ)^19*100000000000000^15 ≤ 37672450039213^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313406777 5000000000 37672450039213 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4454877439/10000000000 : ℝ)^19 ≤ (35908061733121/100000000000000 : ℝ)^15 := by
    have hnat : (4454877439 : ℕ)^19*100000000000000^15 ≤ 35908061733121^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454877439 10000000000 35908061733121 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748213747/5000000000 : ℝ), (2313406777/5000000000 : ℝ), (-4454877439/10000000000 : ℝ)] ![(825609006671/3125000000000 : ℝ), (37672450039213/100000000000000 : ℝ), (35908061733121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748213747/5000000000 : ℝ)|^19 ≤ (825609006671/3125000000000 : ℝ)^15
        have hw : |(-1748213747/5000000000 : ℝ)|=(1748213747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2313406777/5000000000 : ℝ)|^19 ≤ (37672450039213/100000000000000 : ℝ)^15
        have hw : |(2313406777/5000000000 : ℝ)|=(2313406777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4454877439/10000000000 : ℝ)|^19 ≤ (35908061733121/100000000000000 : ℝ)^15
        have hw : |(-4454877439/10000000000 : ℝ)|=(4454877439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1141804947/2000000000 : ℝ)*x 0 + (-2471940359/10000000000 : ℝ)*x 1 + (-2123922241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141804947/2000000000 : ℝ)^19 ≤ (24581880826993/50000000000000 : ℝ)^15 := by
    have hnat : (1141804947 : ℕ)^19*50000000000000^15 ≤ 24581880826993^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141804947 2000000000 24581880826993 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2471940359/10000000000 : ℝ)^19 ≤ (17028698326339/100000000000000 : ℝ)^15 := by
    have hnat : (2471940359 : ℕ)^19*100000000000000^15 ≤ 17028698326339^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471940359 10000000000 17028698326339 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123922241/5000000000 : ℝ)^19 ≤ (211297125039/625000000000 : ℝ)^15 := by
    have hnat : (2123922241 : ℕ)^19*625000000000^15 ≤ 211297125039^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123922241 5000000000 211297125039 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1141804947/2000000000 : ℝ), (-2471940359/10000000000 : ℝ), (-2123922241/5000000000 : ℝ)] ![(24581880826993/50000000000000 : ℝ), (17028698326339/100000000000000 : ℝ), (211297125039/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1141804947/2000000000 : ℝ)|^19 ≤ (24581880826993/50000000000000 : ℝ)^15
        have hw : |(1141804947/2000000000 : ℝ)|=(1141804947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2471940359/10000000000 : ℝ)|^19 ≤ (17028698326339/100000000000000 : ℝ)^15
        have hw : |(-2471940359/10000000000 : ℝ)|=(2471940359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123922241/5000000000 : ℝ)|^19 ≤ (211297125039/625000000000 : ℝ)^15
        have hw : |(-2123922241/5000000000 : ℝ)|=(2123922241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (676786527/2000000000 : ℝ)*x 0 + (2435175323/5000000000 : ℝ)*x 1 + (538943149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676786527/2000000000 : ℝ)^19 ≤ (25347443548229/100000000000000 : ℝ)^15 := by
    have hnat : (676786527 : ℕ)^19*100000000000000^15 ≤ 25347443548229^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676786527 2000000000 25347443548229 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435175323/5000000000 : ℝ)^19 ≤ (40201564795399/100000000000000 : ℝ)^15 := by
    have hnat : (2435175323 : ℕ)^19*100000000000000^15 ≤ 40201564795399^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435175323 5000000000 40201564795399 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538943149/1250000000 : ℝ)^19 ≤ (34450991645473/100000000000000 : ℝ)^15 := by
    have hnat : (538943149 : ℕ)^19*100000000000000^15 ≤ 34450991645473^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538943149 1250000000 34450991645473 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676786527/2000000000 : ℝ), (2435175323/5000000000 : ℝ), (538943149/1250000000 : ℝ)] ![(25347443548229/100000000000000 : ℝ), (40201564795399/100000000000000 : ℝ), (34450991645473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676786527/2000000000 : ℝ)|^19 ≤ (25347443548229/100000000000000 : ℝ)^15
        have hw : |(676786527/2000000000 : ℝ)|=(676786527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435175323/5000000000 : ℝ)|^19 ≤ (40201564795399/100000000000000 : ℝ)^15
        have hw : |(2435175323/5000000000 : ℝ)|=(2435175323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538943149/1250000000 : ℝ)|^19 ≤ (34450991645473/100000000000000 : ℝ)^15
        have hw : |(538943149/1250000000 : ℝ)|=(538943149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314030_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4009230393/10000000000 : ℝ)*x 0 + (5507266739/10000000000 : ℝ)*x 1 + (-1491549607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4009230393/10000000000 : ℝ)^19 ≤ (15710160503237/50000000000000 : ℝ)^15 := by
    have hnat : (4009230393 : ℕ)^19*50000000000000^15 ≤ 15710160503237^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009230393 10000000000 15710160503237 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507266739/10000000000 : ℝ)^19 ≤ (23486722274737/50000000000000 : ℝ)^15 := by
    have hnat : (5507266739 : ℕ)^19*50000000000000^15 ≤ 23486722274737^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507266739 10000000000 23486722274737 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491549607/5000000000 : ℝ)^19 ≤ (5401558604947/25000000000000 : ℝ)^15 := by
    have hnat : (1491549607 : ℕ)^19*25000000000000^15 ≤ 5401558604947^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491549607 5000000000 5401558604947 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4009230393/10000000000 : ℝ), (5507266739/10000000000 : ℝ), (-1491549607/5000000000 : ℝ)] ![(15710160503237/50000000000000 : ℝ), (23486722274737/50000000000000 : ℝ), (5401558604947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4009230393/10000000000 : ℝ)|^19 ≤ (15710160503237/50000000000000 : ℝ)^15
        have hw : |(4009230393/10000000000 : ℝ)|=(4009230393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507266739/10000000000 : ℝ)|^19 ≤ (23486722274737/50000000000000 : ℝ)^15
        have hw : |(5507266739/10000000000 : ℝ)|=(5507266739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1491549607/5000000000 : ℝ)|^19 ≤ (5401558604947/25000000000000 : ℝ)^15
        have hw : |(-1491549607/5000000000 : ℝ)|=(1491549607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314030 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-291552539/1000000000 : ℝ)*X 0 0+(1194159339/2500000000 : ℝ)*X 0 1+(-1207677579/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6950906739/10000000000 : ℝ)*X 1 0+(-217670233/2000000000 : ℝ)*X 1 1+(-494485401/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2627013223/10000000000 : ℝ)*X 2 0+(5485573301/10000000000 : ℝ)*X 2 1+(1088169213/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1843191567/5000000000 : ℝ)*X 0 0+(3248642597/5000000000 : ℝ)*X 0 1+(-2097985441/10000000000 : ℝ)*X 0 2+(1843191567/5000000000 : ℝ)*X 1 0+(3248642597/5000000000 : ℝ)*X 1 1+(-2097985441/10000000000 : ℝ)*X 1 2+(1843191567/5000000000 : ℝ)*X 2 0+(3248642597/5000000000 : ℝ)*X 2 1+(-2097985441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-172830353/625000000 : ℝ)*X 0 0+(3816966787/10000000000 : ℝ)*X 0 1+(-234515707/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1834831429/2500000000 : ℝ)*X 1 0+(-92146857/2500000000 : ℝ)*X 1 1+(-3955653061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1725750321/10000000000 : ℝ)*X 2 0+(848465309/1250000000 : ℝ)*X 2 1+(365889467/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2802114427/10000000000 : ℝ)*X 0 0+(1905965379/2500000000 : ℝ)*X 0 1+(-1510246709/10000000000 : ℝ)*X 0 2+(2802114427/10000000000 : ℝ)*X 1 0+(1905965379/2500000000 : ℝ)*X 1 1+(-1510246709/10000000000 : ℝ)*X 1 2+(2802114427/10000000000 : ℝ)*X 2 0+(1905965379/2500000000 : ℝ)*X 2 1+(-1510246709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3444466539/10000000000 : ℝ)*X 0 0+(184429223/400000000 : ℝ)*X 0 1+(-282475287/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1800322211/2500000000 : ℝ)*X 1 0+(-1139020453/10000000000 : ℝ)*X 1 1+(-3623566829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((17003817/80000000 : ℝ)*X 2 0+(26693083/50000000 : ℝ)*X 2 1+(2462654549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1617184207/5000000000 : ℝ)*X 0 0+(6567855407/10000000000 : ℝ)*X 0 1+(-627168469/2500000000 : ℝ)*X 0 2+(1617184207/5000000000 : ℝ)*X 1 0+(6567855407/10000000000 : ℝ)*X 1 1+(-627168469/2500000000 : ℝ)*X 1 2+(1617184207/5000000000 : ℝ)*X 2 0+(6567855407/10000000000 : ℝ)*X 2 1+(-627168469/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1033360299/5000000000 : ℝ)*X 0 0+(2672703629/5000000000 : ℝ)*X 0 1+(-4965112779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1022469973/1250000000 : ℝ)*X 1 0+(-140768311/2500000000 : ℝ)*X 1 1+(-1395279447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1940160451/10000000000 : ℝ)*X 2 0+(5734759363/10000000000 : ℝ)*X 2 1+(233053163/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1165393689/2500000000 : ℝ)*X 0 0+(1497058009/2500000000 : ℝ)*X 0 1+(-318063103/2000000000 : ℝ)*X 0 2+(1165393689/2500000000 : ℝ)*X 1 0+(1497058009/2500000000 : ℝ)*X 1 1+(-318063103/2000000000 : ℝ)*X 1 2+(1165393689/2500000000 : ℝ)*X 2 0+(1497058009/2500000000 : ℝ)*X 2 1+(-318063103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((32443/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32443/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2556166411111558627359/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1000382307071/1000000000000 : ℝ)*(base39) + (1330500539139/1000000000000 : ℝ)*(base49) + (1437100605269/1000000000000 : ℝ)*(base50) + (498270526673/1000000000000 : ℝ)*(base60) + (409075302261/100000000000 : ℝ)*(major_s0_0) + (409075302261/100000000000 : ℝ)*(major_s0_1) + (409075302261/100000000000 : ℝ)*(major_s0_2) + (24866217/500000000000 : ℝ)*(sp_s0_1) + (1160820198901/200000000000 : ℝ)*(sp_s0_7) + (1451015887229/250000000000 : ℝ)*(sp_s0_8) + (1160815953091/200000000000 : ℝ)*(sp_s0_9) + (475478211951/200000000000 : ℝ)*(sp_s0_12) + (2457369/200000000000 : ℝ)*(sp_s0_20) + (6703179/200000000000 : ℝ)*(sp_s0_22) + (475478211951/200000000000 : ℝ)*(f.failure) + (116082265627/20000000000 : ℝ)*(f.sum) + (508942433/2000000000000000000000 : ℝ)*base63 + (562870133159311/1000000000000000000000000000 : ℝ)*base64 + (161844688159311/1000000000000000000000000000 : ℝ)*base66 + (2658275309557/40000000000000000000000000 : ℝ)*base68 + (56256202224559/250000000000000000000000000 : ℝ)*base70 + (233091013640689/1000000000000000000000000000 : ℝ)*base73 + (22138512898443/40000000000000000000000000 : ℝ)*base74 + (11816220341557/40000000000000000000000000 : ℝ)*base76 + (430690943409311/500000000000000000000000000 : ℝ)*base78 + (3381/20000000000000000 : ℝ)*base86 + (3381/20000000000000000 : ℝ)*base88 + (3381/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3229/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(3229/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (67843126849688337/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022849/1000000000000 : ℝ)*(base3) + (669895454009/1000000000000 : ℝ)*(base39) + (305408408597/1000000000000 : ℝ)*(base49) + (34430285253/250000000000 : ℝ)*(base60) + (2867242115479/1000000000000 : ℝ)*(major_s0_0) + (2867242115479/1000000000000 : ℝ)*(major_s0_1) + (2867242115479/1000000000000 : ℝ)*(major_s0_2) + (252400703/250000000000 : ℝ)*(sp_s0_1) + (44896731/1000000000000 : ℝ)*(sp_s0_2) + (154834631/250000000000 : ℝ)*(sp_s0_6) + (254259184303/62500000000 : ℝ)*(sp_s0_13) + (1016784842221/250000000000 : ℝ)*(sp_s0_14) + (4068102052117/1000000000000 : ℝ)*(sp_s0_15) + (1665711397857/1000000000000 : ℝ)*(sp_s0_19) + (166633275923/100000000000 : ℝ)*(f.failure) + (254259184303/62500000000 : ℝ)*(f.sum) + (2151227029/5000000000000000000000 : ℝ)*base63 + (2556575691605429/10000000000000000000000000000 : ℝ)*base64 + (2473351195394571/10000000000000000000000000000 : ℝ)*base67 + (395242557079177/400000000000000000000000000 : ℝ)*base69 + (1113350138656501/2500000000000000000000000000 : ℝ)*base70 + (2939029088605429/10000000000000000000000000000 : ℝ)*base72 + (60830889720823/400000000000000000000000000 : ℝ)*base75 + (48459576759177/400000000000000000000000000 : ℝ)*base77 + (2370869132394571/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4687/10000000000000000 : ℝ)*base87 + (4687/10000000000000000 : ℝ)*base89 + (4687/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-6757/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8179533771381472108977/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246311003199/200000000000 : ℝ)*(base39) + (7535086109/20000000000 : ℝ)*(base50) + (1853193384943/500000000000 : ℝ)*(major_s0_0) + (8072821535101/1000000000000 : ℝ)*(major_s0_1) + (1853193384943/500000000000 : ℝ)*(major_s0_2) + (24469/25000000000 : ℝ)*(sp_s0_0) + (41284993/500000000000 : ℝ)*(sp_s0_2) + (873286953043/200000000000 : ℝ)*(sp_s0_4) + (4696903/250000000000 : ℝ)*(sp_s0_9) + (306149/31250000000 : ℝ)*(sp_s0_12) + (2629379230113/500000000000 : ℝ)*(sp_s0_20) + (5258759438987/1000000000000 : ℝ)*(sp_s0_21) + (1314664520347/250000000000 : ℝ)*(sp_s0_22) + (2154002122803/1000000000000 : ℝ)*(sp_s0_25) + (2154011919571/1000000000000 : ℝ)*(f.failure) + (5258759438987/1000000000000 : ℝ)*(f.sum) + (17190699797709/80000000000000000000000000 : ℝ)*base62 + (690225949995907/5000000000000000000000000000 : ℝ)*base65 + (1509178676894151/10000000000000000000000000000 : ℝ)*base66 + (53682686480591/200000000000000000000000000 : ℝ)*base68 + (329800989504717/1250000000000000000000000000 : ℝ)*base70 + (1095526699495907/5000000000000000000000000000 : ℝ)*base73 + (78131166852637/400000000000000000000000000 : ℝ)*base75 + (33168075959409/200000000000000000000000000 : ℝ)*base77 + (7539336081097663/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (62399/100000000000000000 : ℝ)*base87 + (62399/100000000000000000 : ℝ)*base89 + (62399/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (32443/100000 : ℝ) ^ (37/8 : ℝ) ≤ (109638895283831199/20000000000000000000 : ℝ) := by
    have hpowers : (32443/100000 : ℝ)^37 ≤ (109638895283831199/20000000000000000000 : ℝ)^8 := by
      have hnat : (32443 : ℕ)^37*20000000000000000000^8 ≤ 109638895283831199^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32443 100000 109638895283831199 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32443/100000 : ℝ)) (X := (109638895283831199/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20109638895283831199/20000000000000000000 : ℝ) ≤ (5005913736195877/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (20109638895283831199/20000000000000000000 : ℝ)^8 ≤ (5005913736195877/5000000000000000 : ℝ)^37 := by
      have hnat : (20109638895283831199 : ℕ)^8*5000000000000000^37 ≤ 5005913736195877^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20109638895283831199 20000000000000000000 5005913736195877 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005913736195877/5000000000000000 : ℝ)) (X := (20109638895283831199/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10109638895283831199/10000000000000000000 : ℝ) ≤ (10023604510716221/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (10109638895283831199/10000000000000000000 : ℝ)^8 ≤ (10023604510716221/10000000000000000 : ℝ)^37 := by
      have hnat : (10109638895283831199 : ℕ)^8*10000000000000000^37 ≤ 10023604510716221^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10109638895283831199 10000000000000000000 10023604510716221 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023604510716221/10000000000000000 : ℝ)) (X := (10109638895283831199/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5913736195877/1622150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11777038324467/3244300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (32443/100000 : ℝ)) (alpha := (5913736195877/1622150000000000 : ℝ)) (beta := (11777038324467/3244300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (32443/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5913736195877/1622150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11777038324467/3244300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3229/50000 : ℝ) ^ (37/8 : ℝ) ≤ (78459122540477/25000000000000000000 : ℝ) := by
    have hpowers : (3229/50000 : ℝ)^37 ≤ (78459122540477/25000000000000000000 : ℝ)^8 := by
      have hnat : (3229 : ℕ)^37*25000000000000000000^8 ≤ 78459122540477^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3229 50000 78459122540477 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3229/50000 : ℝ)) (X := (78459122540477/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25000078459122540477/25000000000000000000 : ℝ) ≤ (1250000848205687/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (25000078459122540477/25000000000000000000 : ℝ)^8 ≤ (1250000848205687/1250000000000000 : ℝ)^37 := by
      have hnat : (25000078459122540477 : ℕ)^8*1250000000000000^37 ≤ 1250000848205687^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000078459122540477 25000000000000000000 1250000848205687 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000848205687/1250000000000000 : ℝ)) (X := (25000078459122540477/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12500078459122540477/12500000000000000000 : ℝ) ≤ (10000013571274301/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (12500078459122540477/12500000000000000000 : ℝ)^8 ≤ (10000013571274301/10000000000000000 : ℝ)^37 := by
      have hnat : (12500078459122540477 : ℕ)^8*10000000000000000^37 ≤ 10000013571274301^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500078459122540477 12500000000000000000 10000013571274301 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000013571274301/10000000000000000 : ℝ)) (X := (12500078459122540477/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(848205687/80725000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1357125761/129160000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (3229/50000 : ℝ)) (alpha := (848205687/80725000000000 : ℝ)) (beta := (1357125761/129160000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (3229/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(848205687/80725000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1357125761/129160000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6757/25000 : ℝ) ^ (37/8 : ℝ) ≤ (14723781104846771/6250000000000000000 : ℝ) := by
    have hpowers : (6757/25000 : ℝ)^37 ≤ (14723781104846771/6250000000000000000 : ℝ)^8 := by
      have hnat : (6757 : ℕ)^37*6250000000000000000^8 ≤ 14723781104846771^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6757 25000 14723781104846771 6250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6757/25000 : ℝ)) (X := (14723781104846771/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6264723781104846771/6250000000000000000 : ℝ) ≤ (1000508893641081/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (6264723781104846771/6250000000000000000 : ℝ)^8 ≤ (1000508893641081/1000000000000000 : ℝ)^37 := by
      have hnat : (6264723781104846771 : ℕ)^8*1000000000000000^37 ≤ 1000508893641081^37*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6264723781104846771 6250000000000000000 1000508893641081 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000508893641081/1000000000000000 : ℝ)) (X := (6264723781104846771/6250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3139723781104846771/3125000000000000000 : ℝ) ≤ (10010168507098101/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3139723781104846771/3125000000000000000 : ℝ)^8 ≤ (10010168507098101/10000000000000000 : ℝ)^37 := by
      have hnat : (3139723781104846771 : ℕ)^8*10000000000000000^37 ≤ 10010168507098101^37*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3139723781104846771 3125000000000000000 10010168507098101 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010168507098101/10000000000000000 : ℝ)) (X := (3139723781104846771/3125000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(17548056589/9320000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5079570687291/2702800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (6757/25000 : ℝ)) (alpha := (17548056589/9320000000000 : ℝ)) (beta := (5079570687291/2702800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6757/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(17548056589/9320000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5079570687291/2702800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1748213747/5000000000 : ℝ)*X 0 0+(2313406777/5000000000 : ℝ)*X 0 1+(-4454877439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1141804947/2000000000 : ℝ)*X 1 0+(-2471940359/10000000000 : ℝ)*X 1 1+(-2123922241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((676786527/2000000000 : ℝ)*X 2 0+(2435175323/5000000000 : ℝ)*X 2 1+(538943149/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4009230393/10000000000 : ℝ)*X 0 0+(5507266739/10000000000 : ℝ)*X 0 1+(-1491549607/5000000000 : ℝ)*X 0 2+(4009230393/10000000000 : ℝ)*X 1 0+(5507266739/10000000000 : ℝ)*X 1 1+(-1491549607/5000000000 : ℝ)*X 1 2+(4009230393/10000000000 : ℝ)*X 2 0+(5507266739/10000000000 : ℝ)*X 2 1+(-1491549607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-51285970227013227129065115729748941/7078528263790000000000000000000000 : ℝ) := by norm_num
    linear_combination (163/500000000000 : ℝ)*(base11) + (4179/250000000000 : ℝ)*(base15) + (1867/200000000000 : ℝ)*(base16) + (195119379121/500000000000 : ℝ)*(base39) + (424481603687/500000000000 : ℝ)*(base49) + (502496755703/1000000000000 : ℝ)*(base50) + (13944345713/250000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s1_0) + (860345001329/500000000000 : ℝ)*(major_s1_1) + (172069/100000 : ℝ)*(major_s1_2) + (37735870747/15625000000 : ℝ)*(sp_s1_0) + (96603827977/40000000000 : ℝ)*(sp_s1_1) + (1207547864067/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (603773931369/250000000000 : ℝ)*(f.sum) + (648628060679721/9404462500000000000000000000 : ℝ)*base63 + (2774660252089/4223125000000000000000000 : ℝ)*base64 + (8778416786307/12916000000000000000000000 : ℝ)*base66 + (4077502973/18640000000000000000000 : ℝ)*base69 + (30428676395585207/87686940400000000000000000000 : ℝ)*base70 + (59344134451/6488600000000000000000000 : ℝ)*base73 + (20261028785071/80725000000000000000000000 : ℝ)*base74 + (13844790669963/81107500000000000000000000 : ℝ)*base76 + (174019018499598673/419033788000000000000000000000 : ℝ)*base78 + (1329/500000000000 : ℝ)*base81 + (1329/500000000000 : ℝ)*base85 + (1329/500000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p014_b015 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 ∨ c=31 := by omega
  rcases hc with rfl|rfl
  · exact collision_c314030 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314031 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
