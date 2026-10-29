-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:41:08.813705+00:00
-- url     : https://prove2.me/submissions/0eba677b-f6b8-491b-b422-4ef643c16341

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314086_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314086_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314086_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c314086 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c314086_s0 p hpa hpb X hX
  have h1 := collision_c314086_s1 p hpa hpb X hX h0
  exact collision_c314086_s2 p hpa hpb X hX h1

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
theorem collision_support_c314085_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013639713/5000000000 : ℝ)*x 0 + (-7199446143/10000000000 : ℝ)*x 1 + (1464388161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013639713/5000000000 : ℝ)^75 ≤ (13150975919439/100000000000000 : ℝ)^59 := by
    have hnat : (1013639713 : ℕ)^75*100000000000000^59 ≤ 13150975919439^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013639713 5000000000 13150975919439 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7199446143/10000000000 : ℝ)^75 ≤ (13171357276731/20000000000000 : ℝ)^59 := by
    have hnat : (7199446143 : ℕ)^75*20000000000000^59 ≤ 13171357276731^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7199446143 10000000000 13171357276731 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464388161/5000000000 : ℝ)^75 ≤ (20992237678699/100000000000000 : ℝ)^59 := by
    have hnat : (1464388161 : ℕ)^75*100000000000000^59 ≤ 20992237678699^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464388161 5000000000 20992237678699 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013639713/5000000000 : ℝ), (-7199446143/10000000000 : ℝ), (1464388161/5000000000 : ℝ)] ![(13150975919439/100000000000000 : ℝ), (13171357276731/20000000000000 : ℝ), (20992237678699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013639713/5000000000 : ℝ)|^75 ≤ (13150975919439/100000000000000 : ℝ)^59
        have hw : |(-1013639713/5000000000 : ℝ)|=(1013639713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7199446143/10000000000 : ℝ)|^75 ≤ (13171357276731/20000000000000 : ℝ)^59
        have hw : |(-7199446143/10000000000 : ℝ)|=(7199446143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1464388161/5000000000 : ℝ)|^75 ≤ (20992237678699/100000000000000 : ℝ)^59
        have hw : |(1464388161/5000000000 : ℝ)|=(1464388161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (696814843/1250000000 : ℝ)*x 0 + (2721095989/10000000000 : ℝ)*x 1 + (842200447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (696814843/1250000000 : ℝ)^75 ≤ (47575379671411/100000000000000 : ℝ)^59 := by
    have hnat : (696814843 : ℕ)^75*100000000000000^59 ≤ 47575379671411^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696814843 1250000000 47575379671411 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721095989/10000000000 : ℝ)^75 ≤ (19118510859587/100000000000000 : ℝ)^59 := by
    have hnat : (2721095989 : ℕ)^75*100000000000000^59 ≤ 19118510859587^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721095989 10000000000 19118510859587 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842200447/2000000000 : ℝ)^75 ≤ (16653054728749/50000000000000 : ℝ)^59 := by
    have hnat : (842200447 : ℕ)^75*50000000000000^59 ≤ 16653054728749^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842200447 2000000000 16653054728749 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(696814843/1250000000 : ℝ), (2721095989/10000000000 : ℝ), (842200447/2000000000 : ℝ)] ![(47575379671411/100000000000000 : ℝ), (19118510859587/100000000000000 : ℝ), (16653054728749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(696814843/1250000000 : ℝ)|^75 ≤ (47575379671411/100000000000000 : ℝ)^59
        have hw : |(696814843/1250000000 : ℝ)|=(696814843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721095989/10000000000 : ℝ)|^75 ≤ (19118510859587/100000000000000 : ℝ)^59
        have hw : |(2721095989/10000000000 : ℝ)|=(2721095989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(842200447/2000000000 : ℝ)|^75 ≤ (16653054728749/50000000000000 : ℝ)^59
        have hw : |(842200447/2000000000 : ℝ)|=(842200447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (242467179/625000000 : ℝ)*x 0 + (-804830203/2500000000 : ℝ)*x 1 + (-682269603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242467179/625000000 : ℝ)^75 ≤ (375114414643/1250000000000 : ℝ)^59 := by
    have hnat : (242467179 : ℕ)^75*1250000000000^59 ≤ 375114414643^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242467179 625000000 375114414643 1250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804830203/2500000000 : ℝ)^75 ≤ (591856752427/2500000000000 : ℝ)^59 := by
    have hnat : (804830203 : ℕ)^75*2500000000000^59 ≤ 591856752427^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804830203 2500000000 591856752427 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682269603/1250000000 : ℝ)^75 ≤ (5789572089849/12500000000000 : ℝ)^59 := by
    have hnat : (682269603 : ℕ)^75*12500000000000^59 ≤ 5789572089849^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682269603 1250000000 5789572089849 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(242467179/625000000 : ℝ), (-804830203/2500000000 : ℝ), (-682269603/1250000000 : ℝ)] ![(375114414643/1250000000000 : ℝ), (591856752427/2500000000000 : ℝ), (5789572089849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(242467179/625000000 : ℝ)|^75 ≤ (375114414643/1250000000000 : ℝ)^59
        have hw : |(242467179/625000000 : ℝ)|=(242467179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-804830203/2500000000 : ℝ)|^75 ≤ (591856752427/2500000000000 : ℝ)^59
        have hw : |(-804830203/2500000000 : ℝ)|=(804830203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682269603/1250000000 : ℝ)|^75 ≤ (5789572089849/12500000000000 : ℝ)^59
        have hw : |(-682269603/1250000000 : ℝ)|=(682269603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6750861737/10000000000 : ℝ)*x 0 + (-534854089/2500000000 : ℝ)*x 1 + (3384833033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6750861737/10000000000 : ℝ)^75 ≤ (60685333898591/100000000000000 : ℝ)^59 := by
    have hnat : (6750861737 : ℕ)^75*100000000000000^59 ≤ 60685333898591^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6750861737 10000000000 60685333898591 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534854089/2500000000 : ℝ)^75 ≤ (3520630845313/25000000000000 : ℝ)^59 := by
    have hnat : (534854089 : ℕ)^75*25000000000000^59 ≤ 3520630845313^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534854089 2500000000 3520630845313 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3384833033/10000000000 : ℝ)^75 ≤ (1261607135229/5000000000000 : ℝ)^59 := by
    have hnat : (3384833033 : ℕ)^75*5000000000000^59 ≤ 1261607135229^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3384833033 10000000000 1261607135229 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6750861737/10000000000 : ℝ), (-534854089/2500000000 : ℝ), (3384833033/10000000000 : ℝ)] ![(60685333898591/100000000000000 : ℝ), (3520630845313/25000000000000 : ℝ), (1261607135229/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6750861737/10000000000 : ℝ)|^75 ≤ (60685333898591/100000000000000 : ℝ)^59
        have hw : |(6750861737/10000000000 : ℝ)|=(6750861737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534854089/2500000000 : ℝ)|^75 ≤ (3520630845313/25000000000000 : ℝ)^59
        have hw : |(-534854089/2500000000 : ℝ)|=(534854089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3384833033/10000000000 : ℝ)|^75 ≤ (1261607135229/5000000000000 : ℝ)^59
        have hw : |(3384833033/10000000000 : ℝ)|=(3384833033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854343809/10000000000 : ℝ)*x 0 + (-7524173309/10000000000 : ℝ)*x 1 + (2663167167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854343809/10000000000 : ℝ)^75 ≤ (5870882439407/50000000000000 : ℝ)^59 := by
    have hnat : (1854343809 : ℕ)^75*50000000000000^59 ≤ 5870882439407^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854343809 10000000000 5870882439407 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7524173309/10000000000 : ℝ)^75 ≤ (34827804165957/50000000000000 : ℝ)^59 := by
    have hnat : (7524173309 : ℕ)^75*50000000000000^59 ≤ 34827804165957^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7524173309 10000000000 34827804165957 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663167167/10000000000 : ℝ)^75 ≤ (18602626772287/100000000000000 : ℝ)^59 := by
    have hnat : (2663167167 : ℕ)^75*100000000000000^59 ≤ 18602626772287^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663167167 10000000000 18602626772287 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854343809/10000000000 : ℝ), (-7524173309/10000000000 : ℝ), (2663167167/10000000000 : ℝ)] ![(5870882439407/50000000000000 : ℝ), (34827804165957/50000000000000 : ℝ), (18602626772287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854343809/10000000000 : ℝ)|^75 ≤ (5870882439407/50000000000000 : ℝ)^59
        have hw : |(-1854343809/10000000000 : ℝ)|=(1854343809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7524173309/10000000000 : ℝ)|^75 ≤ (34827804165957/50000000000000 : ℝ)^59
        have hw : |(-7524173309/10000000000 : ℝ)|=(7524173309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663167167/10000000000 : ℝ)|^75 ≤ (18602626772287/100000000000000 : ℝ)^59
        have hw : |(2663167167/10000000000 : ℝ)|=(2663167167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (281419763/500000000 : ℝ)*x 0 + (2601091787/10000000000 : ℝ)*x 1 + (4258676747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281419763/500000000 : ℝ)^75 ≤ (48160642673171/100000000000000 : ℝ)^59 := by
    have hnat : (281419763 : ℕ)^75*100000000000000^59 ≤ 48160642673171^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281419763 500000000 48160642673171 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601091787/10000000000 : ℝ)^75 ≤ (9026592398127/50000000000000 : ℝ)^59 := by
    have hnat : (2601091787 : ℕ)^75*50000000000000^59 ≤ 9026592398127^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601091787 10000000000 9026592398127 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4258676747/10000000000 : ℝ)^75 ≤ (16893086262913/50000000000000 : ℝ)^59 := by
    have hnat : (4258676747 : ℕ)^75*50000000000000^59 ≤ 16893086262913^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258676747 10000000000 16893086262913 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(281419763/500000000 : ℝ), (2601091787/10000000000 : ℝ), (4258676747/10000000000 : ℝ)] ![(48160642673171/100000000000000 : ℝ), (9026592398127/50000000000000 : ℝ), (16893086262913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(281419763/500000000 : ℝ)|^75 ≤ (48160642673171/100000000000000 : ℝ)^59
        have hw : |(281419763/500000000 : ℝ)|=(281419763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601091787/10000000000 : ℝ)|^75 ≤ (9026592398127/50000000000000 : ℝ)^59
        have hw : |(2601091787/10000000000 : ℝ)|=(2601091787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4258676747/10000000000 : ℝ)|^75 ≤ (16893086262913/50000000000000 : ℝ)^59
        have hw : |(4258676747/10000000000 : ℝ)|=(4258676747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3980518501/10000000000 : ℝ)*x 0 + (-1499164499/5000000000 : ℝ)*x 1 + (-1111038389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3980518501/10000000000 : ℝ)^75 ≤ (31006211389411/100000000000000 : ℝ)^59 := by
    have hnat : (3980518501 : ℕ)^75*100000000000000^59 ≤ 31006211389411^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980518501 10000000000 31006211389411 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499164499/5000000000 : ℝ)^75 ≤ (21627984032127/100000000000000 : ℝ)^59 := by
    have hnat : (1499164499 : ℕ)^75*100000000000000^59 ≤ 21627984032127^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499164499 5000000000 21627984032127 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111038389/2000000000 : ℝ)^75 ≤ (47365804571339/100000000000000 : ℝ)^59 := by
    have hnat : (1111038389 : ℕ)^75*100000000000000^59 ≤ 47365804571339^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111038389 2000000000 47365804571339 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3980518501/10000000000 : ℝ), (-1499164499/5000000000 : ℝ), (-1111038389/2000000000 : ℝ)] ![(31006211389411/100000000000000 : ℝ), (21627984032127/100000000000000 : ℝ), (47365804571339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3980518501/10000000000 : ℝ)|^75 ≤ (31006211389411/100000000000000 : ℝ)^59
        have hw : |(3980518501/10000000000 : ℝ)|=(3980518501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499164499/5000000000 : ℝ)|^75 ≤ (21627984032127/100000000000000 : ℝ)^59
        have hw : |(-1499164499/5000000000 : ℝ)|=(1499164499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111038389/2000000000 : ℝ)|^75 ≤ (47365804571339/100000000000000 : ℝ)^59
        have hw : |(-1111038389/2000000000 : ℝ)|=(1111038389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6905092119/10000000000 : ℝ)*x 0 + (-485549619/2500000000 : ℝ)*x 1 + (421273189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6905092119/10000000000 : ℝ)^75 ≤ (1561329007001/2500000000000 : ℝ)^59 := by
    have hnat : (6905092119 : ℕ)^75*2500000000000^59 ≤ 1561329007001^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6905092119 10000000000 1561329007001 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485549619/2500000000 : ℝ)^75 ≤ (2490683144357/20000000000000 : ℝ)^59 := by
    have hnat : (485549619 : ℕ)^75*20000000000000^59 ≤ 2490683144357^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485549619 2500000000 2490683144357 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421273189/1250000000 : ℝ)^75 ≤ (25093423979057/100000000000000 : ℝ)^59 := by
    have hnat : (421273189 : ℕ)^75*100000000000000^59 ≤ 25093423979057^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421273189 1250000000 25093423979057 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6905092119/10000000000 : ℝ), (-485549619/2500000000 : ℝ), (421273189/1250000000 : ℝ)] ![(1561329007001/2500000000000 : ℝ), (2490683144357/20000000000000 : ℝ), (25093423979057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6905092119/10000000000 : ℝ)|^75 ≤ (1561329007001/2500000000000 : ℝ)^59
        have hw : |(6905092119/10000000000 : ℝ)|=(6905092119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485549619/2500000000 : ℝ)|^75 ≤ (2490683144357/20000000000000 : ℝ)^59
        have hw : |(-485549619/2500000000 : ℝ)|=(485549619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421273189/1250000000 : ℝ)|^75 ≤ (25093423979057/100000000000000 : ℝ)^59
        have hw : |(421273189/1250000000 : ℝ)|=(421273189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-62900219/312500000 : ℝ)*x 0 + (-1439615419/2000000000 : ℝ)*x 1 + (2943598877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62900219/312500000 : ℝ)^75 ≤ (13031749254513/100000000000000 : ℝ)^59 := by
    have hnat : (62900219 : ℕ)^75*100000000000000^59 ≤ 13031749254513^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62900219 312500000 13031749254513 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439615419/2000000000 : ℝ)^75 ≤ (13168173459189/20000000000000 : ℝ)^59 := by
    have hnat : (1439615419 : ℕ)^75*20000000000000^59 ≤ 13168173459189^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439615419 2000000000 13168173459189 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2943598877/10000000000 : ℝ)^75 ≤ (21127383435369/100000000000000 : ℝ)^59 := by
    have hnat : (2943598877 : ℕ)^75*100000000000000^59 ≤ 21127383435369^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2943598877 10000000000 21127383435369 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62900219/312500000 : ℝ), (-1439615419/2000000000 : ℝ), (2943598877/10000000000 : ℝ)] ![(13031749254513/100000000000000 : ℝ), (13168173459189/20000000000000 : ℝ), (21127383435369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62900219/312500000 : ℝ)|^75 ≤ (13031749254513/100000000000000 : ℝ)^59
        have hw : |(-62900219/312500000 : ℝ)|=(62900219/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439615419/2000000000 : ℝ)|^75 ≤ (13168173459189/20000000000000 : ℝ)^59
        have hw : |(-1439615419/2000000000 : ℝ)|=(1439615419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2943598877/10000000000 : ℝ)|^75 ≤ (21127383435369/100000000000000 : ℝ)^59
        have hw : |(2943598877/10000000000 : ℝ)|=(2943598877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5337156871/10000000000 : ℝ)*x 0 + (176927019/625000000 : ℝ)*x 1 + (4366845709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337156871/10000000000 : ℝ)^75 ≤ (2250764895609/5000000000000 : ℝ)^59 := by
    have hnat : (5337156871 : ℕ)^75*5000000000000^59 ≤ 2250764895609^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337156871 10000000000 2250764895609 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176927019/625000000 : ℝ)^75 ≤ (10051958674817/50000000000000 : ℝ)^59 := by
    have hnat : (176927019 : ℕ)^75*50000000000000^59 ≤ 10051958674817^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176927019 625000000 10051958674817 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4366845709/10000000000 : ℝ)^75 ≤ (17440392363711/50000000000000 : ℝ)^59 := by
    have hnat : (4366845709 : ℕ)^75*50000000000000^59 ≤ 17440392363711^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366845709 10000000000 17440392363711 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337156871/10000000000 : ℝ), (176927019/625000000 : ℝ), (4366845709/10000000000 : ℝ)] ![(2250764895609/5000000000000 : ℝ), (10051958674817/50000000000000 : ℝ), (17440392363711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337156871/10000000000 : ℝ)|^75 ≤ (2250764895609/5000000000000 : ℝ)^59
        have hw : |(5337156871/10000000000 : ℝ)|=(5337156871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176927019/625000000 : ℝ)|^75 ≤ (10051958674817/50000000000000 : ℝ)^59
        have hw : |(176927019/625000000 : ℝ)|=(176927019/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4366845709/10000000000 : ℝ)|^75 ≤ (17440392363711/50000000000000 : ℝ)^59
        have hw : |(4366845709/10000000000 : ℝ)|=(4366845709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (486958917/1250000000 : ℝ)*x 0 + (-3218366821/10000000000 : ℝ)*x 1 + (-1361051527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486958917/1250000000 : ℝ)^75 ≤ (15084252308153/50000000000000 : ℝ)^59 := by
    have hnat : (486958917 : ℕ)^75*50000000000000^59 ≤ 15084252308153^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486958917 1250000000 15084252308153 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3218366821/10000000000 : ℝ)^75 ≤ (11832676244123/50000000000000 : ℝ)^59 := by
    have hnat : (3218366821 : ℕ)^75*50000000000000^59 ≤ 11832676244123^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3218366821 10000000000 11832676244123 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361051527/2500000000 : ℝ)^75 ≤ (5770767859027/12500000000000 : ℝ)^59 := by
    have hnat : (1361051527 : ℕ)^75*12500000000000^59 ≤ 5770767859027^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361051527 2500000000 5770767859027 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486958917/1250000000 : ℝ), (-3218366821/10000000000 : ℝ), (-1361051527/2500000000 : ℝ)] ![(15084252308153/50000000000000 : ℝ), (11832676244123/50000000000000 : ℝ), (5770767859027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486958917/1250000000 : ℝ)|^75 ≤ (15084252308153/50000000000000 : ℝ)^59
        have hw : |(486958917/1250000000 : ℝ)|=(486958917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3218366821/10000000000 : ℝ)|^75 ≤ (11832676244123/50000000000000 : ℝ)^59
        have hw : |(-3218366821/10000000000 : ℝ)|=(3218366821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361051527/2500000000 : ℝ)|^75 ≤ (5770767859027/12500000000000 : ℝ)^59
        have hw : |(-1361051527/2500000000 : ℝ)|=(1361051527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (366964241/500000000 : ℝ)*x 0 + (-861665543/5000000000 : ℝ)*x 1 + (603749543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366964241/500000000 : ℝ)^75 ≤ (67487114298623/100000000000000 : ℝ)^59 := by
    have hnat : (366964241 : ℕ)^75*100000000000000^59 ≤ 67487114298623^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366964241 500000000 67487114298623 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861665543/5000000000 : ℝ)^75 ≤ (2139499894611/20000000000000 : ℝ)^59 := by
    have hnat : (861665543 : ℕ)^75*20000000000000^59 ≤ 2139499894611^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861665543 5000000000 2139499894611 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603749543/2000000000 : ℝ)^75 ≤ (21815386210997/100000000000000 : ℝ)^59 := by
    have hnat : (603749543 : ℕ)^75*100000000000000^59 ≤ 21815386210997^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603749543 2000000000 21815386210997 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(366964241/500000000 : ℝ), (-861665543/5000000000 : ℝ), (603749543/2000000000 : ℝ)] ![(67487114298623/100000000000000 : ℝ), (2139499894611/20000000000000 : ℝ), (21815386210997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(366964241/500000000 : ℝ)|^75 ≤ (67487114298623/100000000000000 : ℝ)^59
        have hw : |(366964241/500000000 : ℝ)|=(366964241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-861665543/5000000000 : ℝ)|^75 ≤ (2139499894611/20000000000000 : ℝ)^59
        have hw : |(-861665543/5000000000 : ℝ)|=(861665543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603749543/2000000000 : ℝ)|^75 ≤ (21815386210997/100000000000000 : ℝ)^59
        have hw : |(603749543/2000000000 : ℝ)|=(603749543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-466203123/2500000000 : ℝ)*x 0 + (-7350047791/10000000000 : ℝ)*x 1 + (2881337377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466203123/2500000000 : ℝ)^75 ≤ (11826093750311/100000000000000 : ℝ)^59 := by
    have hnat : (466203123 : ℕ)^75*100000000000000^59 ≤ 11826093750311^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466203123 2500000000 11826093750311 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7350047791/10000000000 : ℝ)^75 ≤ (67612947387233/100000000000000 : ℝ)^59 := by
    have hnat : (7350047791 : ℕ)^75*100000000000000^59 ≤ 67612947387233^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7350047791 10000000000 67612947387233 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2881337377/10000000000 : ℝ)^75 ≤ (20560958852723/100000000000000 : ℝ)^59 := by
    have hnat : (2881337377 : ℕ)^75*100000000000000^59 ≤ 20560958852723^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881337377 10000000000 20560958852723 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466203123/2500000000 : ℝ), (-7350047791/10000000000 : ℝ), (2881337377/10000000000 : ℝ)] ![(11826093750311/100000000000000 : ℝ), (67612947387233/100000000000000 : ℝ), (20560958852723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466203123/2500000000 : ℝ)|^75 ≤ (11826093750311/100000000000000 : ℝ)^59
        have hw : |(-466203123/2500000000 : ℝ)|=(466203123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7350047791/10000000000 : ℝ)|^75 ≤ (67612947387233/100000000000000 : ℝ)^59
        have hw : |(-7350047791/10000000000 : ℝ)|=(7350047791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2881337377/10000000000 : ℝ)|^75 ≤ (20560958852723/100000000000000 : ℝ)^59
        have hw : |(2881337377/10000000000 : ℝ)|=(2881337377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1432683899/2500000000 : ℝ)*x 0 + (663604389/2500000000 : ℝ)*x 1 + (1025110049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1432683899/2500000000 : ℝ)^75 ≤ (49276550997533/100000000000000 : ℝ)^59 := by
    have hnat : (1432683899 : ℕ)^75*100000000000000^59 ≤ 49276550997533^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432683899 2500000000 49276550997533 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (663604389/2500000000 : ℝ)^75 ≤ (18524969850027/100000000000000 : ℝ)^59 := by
    have hnat : (663604389 : ℕ)^75*100000000000000^59 ≤ 18524969850027^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663604389 2500000000 18524969850027 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025110049/2500000000 : ℝ)^75 ≤ (4024809892153/12500000000000 : ℝ)^59 := by
    have hnat : (1025110049 : ℕ)^75*12500000000000^59 ≤ 4024809892153^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025110049 2500000000 4024809892153 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1432683899/2500000000 : ℝ), (663604389/2500000000 : ℝ), (1025110049/2500000000 : ℝ)] ![(49276550997533/100000000000000 : ℝ), (18524969850027/100000000000000 : ℝ), (4024809892153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1432683899/2500000000 : ℝ)|^75 ≤ (49276550997533/100000000000000 : ℝ)^59
        have hw : |(1432683899/2500000000 : ℝ)|=(1432683899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(663604389/2500000000 : ℝ)|^75 ≤ (18524969850027/100000000000000 : ℝ)^59
        have hw : |(663604389/2500000000 : ℝ)|=(663604389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025110049/2500000000 : ℝ)|^75 ≤ (4024809892153/12500000000000 : ℝ)^59
        have hw : |(1025110049/2500000000 : ℝ)|=(1025110049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (748980587/2000000000 : ℝ)*x 0 + (-3250860431/10000000000 : ℝ)*x 1 + (-5552657147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748980587/2000000000 : ℝ)^75 ≤ (28692172345483/100000000000000 : ℝ)^59 := by
    have hnat : (748980587 : ℕ)^75*100000000000000^59 ≤ 28692172345483^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748980587 2000000000 28692172345483 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3250860431/10000000000 : ℝ)^75 ≤ (1198474757379/5000000000000 : ℝ)^59 := by
    have hnat : (3250860431 : ℕ)^75*5000000000000^59 ≤ 1198474757379^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3250860431 10000000000 1198474757379 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5552657147/10000000000 : ℝ)^75 ≤ (47338332488769/100000000000000 : ℝ)^59 := by
    have hnat : (5552657147 : ℕ)^75*100000000000000^59 ≤ 47338332488769^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5552657147 10000000000 47338332488769 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(748980587/2000000000 : ℝ), (-3250860431/10000000000 : ℝ), (-5552657147/10000000000 : ℝ)] ![(28692172345483/100000000000000 : ℝ), (1198474757379/5000000000000 : ℝ), (47338332488769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(748980587/2000000000 : ℝ)|^75 ≤ (28692172345483/100000000000000 : ℝ)^59
        have hw : |(748980587/2000000000 : ℝ)|=(748980587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3250860431/10000000000 : ℝ)|^75 ≤ (1198474757379/5000000000000 : ℝ)^59
        have hw : |(-3250860431/10000000000 : ℝ)|=(3250860431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5552657147/10000000000 : ℝ)|^75 ≤ (47338332488769/100000000000000 : ℝ)^59
        have hw : |(-5552657147/10000000000 : ℝ)|=(5552657147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s0_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7290650469/10000000000 : ℝ)*x 0 + (-1712401927/10000000000 : ℝ)*x 1 + (3089730109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7290650469/10000000000 : ℝ)^75 ≤ (8364892535769/12500000000000 : ℝ)^59 := by
    have hnat : (7290650469 : ℕ)^75*12500000000000^59 ≤ 8364892535769^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7290650469 10000000000 8364892535769 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1712401927/10000000000 : ℝ)^75 ≤ (5305666794039/50000000000000 : ℝ)^59 := by
    have hnat : (1712401927 : ℕ)^75*50000000000000^59 ≤ 5305666794039^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712401927 10000000000 5305666794039 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3089730109/10000000000 : ℝ)^75 ≤ (11234763056883/50000000000000 : ℝ)^59 := by
    have hnat : (3089730109 : ℕ)^75*50000000000000^59 ≤ 11234763056883^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089730109 10000000000 11234763056883 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7290650469/10000000000 : ℝ), (-1712401927/10000000000 : ℝ), (3089730109/10000000000 : ℝ)] ![(8364892535769/12500000000000 : ℝ), (5305666794039/50000000000000 : ℝ), (11234763056883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7290650469/10000000000 : ℝ)|^75 ≤ (8364892535769/12500000000000 : ℝ)^59
        have hw : |(7290650469/10000000000 : ℝ)|=(7290650469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1712401927/10000000000 : ℝ)|^75 ≤ (5305666794039/50000000000000 : ℝ)^59
        have hw : |(-1712401927/10000000000 : ℝ)|=(1712401927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3089730109/10000000000 : ℝ)|^75 ≤ (11234763056883/50000000000000 : ℝ)^59
        have hw : |(3089730109/10000000000 : ℝ)|=(3089730109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-803374513/2500000000 : ℝ)*x 0 + (-5430498823/10000000000 : ℝ)*x 1 + (3915284497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (803374513/2500000000 : ℝ)^75 ≤ (23619851929523/100000000000000 : ℝ)^59 := by
    have hnat : (803374513 : ℕ)^75*100000000000000^59 ≤ 23619851929523^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803374513 2500000000 23619851929523 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430498823/10000000000 : ℝ)^75 ≤ (46018435780931/100000000000000 : ℝ)^59 := by
    have hnat : (5430498823 : ℕ)^75*100000000000000^59 ≤ 46018435780931^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430498823 10000000000 46018435780931 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3915284497/10000000000 : ℝ)^75 ≤ (30361712271967/100000000000000 : ℝ)^59 := by
    have hnat : (3915284497 : ℕ)^75*100000000000000^59 ≤ 30361712271967^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3915284497 10000000000 30361712271967 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-803374513/2500000000 : ℝ), (-5430498823/10000000000 : ℝ), (3915284497/10000000000 : ℝ)] ![(23619851929523/100000000000000 : ℝ), (46018435780931/100000000000000 : ℝ), (30361712271967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-803374513/2500000000 : ℝ)|^75 ≤ (23619851929523/100000000000000 : ℝ)^59
        have hw : |(-803374513/2500000000 : ℝ)|=(803374513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5430498823/10000000000 : ℝ)|^75 ≤ (46018435780931/100000000000000 : ℝ)^59
        have hw : |(-5430498823/10000000000 : ℝ)|=(5430498823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3915284497/10000000000 : ℝ)|^75 ≤ (30361712271967/100000000000000 : ℝ)^59
        have hw : |(3915284497/10000000000 : ℝ)|=(3915284497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5210329539/10000000000 : ℝ)*x 0 + (411963397/1250000000 : ℝ)*x 1 + (2037736651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5210329539/10000000000 : ℝ)^75 ≤ (21829956768689/50000000000000 : ℝ)^59 := by
    have hnat : (5210329539 : ℕ)^75*50000000000000^59 ≤ 21829956768689^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210329539 10000000000 21829956768689 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411963397/1250000000 : ℝ)^75 ≤ (24390618818267/100000000000000 : ℝ)^59 := by
    have hnat : (411963397 : ℕ)^75*100000000000000^59 ≤ 24390618818267^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411963397 1250000000 24390618818267 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037736651/5000000000 : ℝ)^75 ≤ (15974733817027/50000000000000 : ℝ)^59 := by
    have hnat : (2037736651 : ℕ)^75*50000000000000^59 ≤ 15974733817027^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037736651 5000000000 15974733817027 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5210329539/10000000000 : ℝ), (411963397/1250000000 : ℝ), (2037736651/5000000000 : ℝ)] ![(21829956768689/50000000000000 : ℝ), (24390618818267/100000000000000 : ℝ), (15974733817027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5210329539/10000000000 : ℝ)|^75 ≤ (21829956768689/50000000000000 : ℝ)^59
        have hw : |(5210329539/10000000000 : ℝ)|=(5210329539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411963397/1250000000 : ℝ)|^75 ≤ (24390618818267/100000000000000 : ℝ)^59
        have hw : |(411963397/1250000000 : ℝ)|=(411963397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2037736651/5000000000 : ℝ)|^75 ≤ (15974733817027/50000000000000 : ℝ)^59
        have hw : |(2037736651/5000000000 : ℝ)|=(2037736651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3947929713/10000000000 : ℝ)*x 0 + (-3865731799/10000000000 : ℝ)*x 1 + (-240505327/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3947929713/10000000000 : ℝ)^75 ≤ (30683879576257/100000000000000 : ℝ)^59 := by
    have hnat : (3947929713 : ℕ)^75*100000000000000^59 ≤ 30683879576257^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3947929713 10000000000 30683879576257 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3865731799/10000000000 : ℝ)^75 ≤ (29874081332921/100000000000000 : ℝ)^59 := by
    have hnat : (3865731799 : ℕ)^75*100000000000000^59 ≤ 29874081332921^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865731799 10000000000 29874081332921 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240505327/500000000 : ℝ)^75 ≤ (39442039074941/100000000000000 : ℝ)^59 := by
    have hnat : (240505327 : ℕ)^75*100000000000000^59 ≤ 39442039074941^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240505327 500000000 39442039074941 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3947929713/10000000000 : ℝ), (-3865731799/10000000000 : ℝ), (-240505327/500000000 : ℝ)] ![(30683879576257/100000000000000 : ℝ), (29874081332921/100000000000000 : ℝ), (39442039074941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3947929713/10000000000 : ℝ)|^75 ≤ (30683879576257/100000000000000 : ℝ)^59
        have hw : |(3947929713/10000000000 : ℝ)|=(3947929713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3865731799/10000000000 : ℝ)|^75 ≤ (29874081332921/100000000000000 : ℝ)^59
        have hw : |(-3865731799/10000000000 : ℝ)|=(3865731799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240505327/500000000 : ℝ)|^75 ≤ (39442039074941/100000000000000 : ℝ)^59
        have hw : |(-240505327/500000000 : ℝ)|=(240505327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314085_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (590917561/1250000000 : ℝ)*x 0 + (-4199009573/10000000000 : ℝ)*x 1 + (3697683573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590917561/1250000000 : ℝ)^75 ≤ (4822668466239/12500000000000 : ℝ)^59 := by
    have hnat : (590917561 : ℕ)^75*12500000000000^59 ≤ 4822668466239^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590917561 1250000000 4822668466239 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4199009573/10000000000 : ℝ)^75 ≤ (33185579383699/100000000000000 : ℝ)^59 := by
    have hnat : (4199009573 : ℕ)^75*100000000000000^59 ≤ 33185579383699^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199009573 10000000000 33185579383699 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3697683573/10000000000 : ℝ)^75 ≤ (1764567054391/6250000000000 : ℝ)^59 := by
    have hnat : (3697683573 : ℕ)^75*6250000000000^59 ≤ 1764567054391^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697683573 10000000000 1764567054391 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(590917561/1250000000 : ℝ), (-4199009573/10000000000 : ℝ), (3697683573/10000000000 : ℝ)] ![(4822668466239/12500000000000 : ℝ), (33185579383699/100000000000000 : ℝ), (1764567054391/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(590917561/1250000000 : ℝ)|^75 ≤ (4822668466239/12500000000000 : ℝ)^59
        have hw : |(590917561/1250000000 : ℝ)|=(590917561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4199009573/10000000000 : ℝ)|^75 ≤ (33185579383699/100000000000000 : ℝ)^59
        have hw : |(-4199009573/10000000000 : ℝ)|=(4199009573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3697683573/10000000000 : ℝ)|^75 ≤ (1764567054391/6250000000000 : ℝ)^59
        have hw : |(3697683573/10000000000 : ℝ)|=(3697683573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314085 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
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
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1013639713/5000000000 : ℝ)*X 0 0+(-7199446143/10000000000 : ℝ)*X 0 1+(1464388161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((696814843/1250000000 : ℝ)*X 1 0+(2721095989/10000000000 : ℝ)*X 1 1+(842200447/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((242467179/625000000 : ℝ)*X 2 0+(-804830203/2500000000 : ℝ)*X 2 1+(-682269603/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6750861737/10000000000 : ℝ)*X 0 0+(-534854089/2500000000 : ℝ)*X 0 1+(3384833033/10000000000 : ℝ)*X 0 2+(6750861737/10000000000 : ℝ)*X 1 0+(-534854089/2500000000 : ℝ)*X 1 1+(3384833033/10000000000 : ℝ)*X 1 2+(6750861737/10000000000 : ℝ)*X 2 0+(-534854089/2500000000 : ℝ)*X 2 1+(3384833033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1854343809/10000000000 : ℝ)*X 0 0+(-7524173309/10000000000 : ℝ)*X 0 1+(2663167167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((281419763/500000000 : ℝ)*X 1 0+(2601091787/10000000000 : ℝ)*X 1 1+(4258676747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3980518501/10000000000 : ℝ)*X 2 0+(-1499164499/5000000000 : ℝ)*X 2 1+(-1111038389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((6905092119/10000000000 : ℝ)*X 0 0+(-485549619/2500000000 : ℝ)*X 0 1+(421273189/1250000000 : ℝ)*X 0 2+(6905092119/10000000000 : ℝ)*X 1 0+(-485549619/2500000000 : ℝ)*X 1 1+(421273189/1250000000 : ℝ)*X 1 2+(6905092119/10000000000 : ℝ)*X 2 0+(-485549619/2500000000 : ℝ)*X 2 1+(421273189/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-62900219/312500000 : ℝ)*X 0 0+(-1439615419/2000000000 : ℝ)*X 0 1+(2943598877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5337156871/10000000000 : ℝ)*X 1 0+(176927019/625000000 : ℝ)*X 1 1+(4366845709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((486958917/1250000000 : ℝ)*X 2 0+(-3218366821/10000000000 : ℝ)*X 2 1+(-1361051527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((366964241/500000000 : ℝ)*X 0 0+(-861665543/5000000000 : ℝ)*X 0 1+(603749543/2000000000 : ℝ)*X 0 2+(366964241/500000000 : ℝ)*X 1 0+(-861665543/5000000000 : ℝ)*X 1 1+(603749543/2000000000 : ℝ)*X 1 2+(366964241/500000000 : ℝ)*X 2 0+(-861665543/5000000000 : ℝ)*X 2 1+(603749543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-466203123/2500000000 : ℝ)*X 0 0+(-7350047791/10000000000 : ℝ)*X 0 1+(2881337377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1432683899/2500000000 : ℝ)*X 1 0+(663604389/2500000000 : ℝ)*X 1 1+(1025110049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((748980587/2000000000 : ℝ)*X 2 0+(-3250860431/10000000000 : ℝ)*X 2 1+(-5552657147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7290650469/10000000000 : ℝ)*X 0 0+(-1712401927/10000000000 : ℝ)*X 0 1+(3089730109/10000000000 : ℝ)*X 0 2+(7290650469/10000000000 : ℝ)*X 1 0+(-1712401927/10000000000 : ℝ)*X 1 1+(3089730109/10000000000 : ℝ)*X 1 2+(7290650469/10000000000 : ℝ)*X 2 0+(-1712401927/10000000000 : ℝ)*X 2 1+(3089730109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((643/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(643/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17736545747275771048233/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469038565159/125000000000 : ℝ)*(base3) + (1341951287613/500000000000 : ℝ)*(base40) + (3870710907713/1000000000000 : ℝ)*(base50) + (4924735362943/500000000000 : ℝ)*(major_s0_0) + (4924735362943/500000000000 : ℝ)*(major_s0_1) + (4924735362943/500000000000 : ℝ)*(major_s0_2) + (52541767/500000000000 : ℝ)*(sp_s0_6) + (13974658935809/1000000000000 : ℝ)*(sp_s0_7) + (8863517399811/500000000000 : ℝ)*(sp_s0_8) + (6987348981797/500000000000 : ℝ)*(sp_s0_9) + (1971726551693/1000000000000 : ℝ)*(sp_s0_13) + (72652043/1000000000000 : ℝ)*(sp_s0_15) + (27998917/200000000000 : ℝ)*(sp_s0_21) + (100966799/1000000000000 : ℝ)*(sp_s0_23) + (5724140156499/1000000000000 : ℝ)*(f.failure) + (6987399465197/500000000000 : ℝ)*(f.sum) + (479498631613283/1250000000000000000000000000 : ℝ)*base63 + (1375558014882093/5000000000000000000000000000 : ℝ)*base65 + (66947195906591/200000000000000000000000000 : ℝ)*base67 + (55918558413409/200000000000000000000000000 : ℝ)*base69 + (525804038391341/2500000000000000000000000000 : ℝ)*base70 + (3676123049617907/5000000000000000000000000000 : ℝ)*base73 + (3032032987117907/5000000000000000000000000000 : ℝ)*base75 + (130641314566591/200000000000000000000000000 : ℝ)*base76 + (1227969721141341/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (26431/100000000000000000 : ℝ)*base87 + (26431/100000000000000000 : ℝ)*base89 + (26431/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-5719/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-5719/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16940685693341421/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (1569336566219/1000000000000 : ℝ)*(base3) + (843001533609/200000000000 : ℝ)*(base40) + (2959501863223/1000000000000 : ℝ)*(base50) + (1744727/500000000000 : ℝ)*(base59) + (7107136422911/500000000000 : ℝ)*(major_s0_0) + (7107136422911/500000000000 : ℝ)*(major_s0_1) + (7107136422911/500000000000 : ℝ)*(major_s0_2) + (384013991/1000000000000 : ℝ)*(sp_s0_1) + (59699039/200000000000 : ℝ)*(sp_s0_9) + (10083870924969/500000000000 : ℝ)*(sp_s0_14) + (10868347201083/500000000000 : ℝ)*(sp_s0_15) + (2520930419343/125000000000 : ℝ)*(sp_s0_16) + (83626382443/12500000000 : ℝ)*(sp_s0_20) + (337758287/250000000000 : ℝ)*(sp_s0_27) + (8260798194807/1000000000000 : ℝ)*(f.failure) + (10083870924969/500000000000 : ℝ)*(f.sum) + (41658199893091/1250000000000000000000000000 : ℝ)*base63 + (2452221716587539/5000000000000000000000000000 : ℝ)*base64 + (64589558280607/200000000000000000000000000 : ℝ)*base67 + (7935347480607/200000000000000000000000000 : ℝ)*base68 + (322340905448643/2500000000000000000000000000 : ℝ)*base71 + (1182205365912461/5000000000000000000000000000 : ℝ)*base72 + (872075155912461/5000000000000000000000000000 : ℝ)*base74 + (114035343959393/200000000000000000000000000 : ℝ)*base77 + (789228936551357/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (45683/100000000000000000 : ℝ)*base87 + (45683/100000000000000000 : ℝ)*base89 + (45683/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24531/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24531/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (341821123608958296807/20000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4950015182537/1000000000000 : ℝ)*(base3) + (739539276571/100000000000 : ℝ)*(base40) + (7180395748237/1000000000000 : ℝ)*(base50) + (4718176806163/200000000000 : ℝ)*(major_s0_0) + (4718176806163/200000000000 : ℝ)*(major_s0_1) + (4718176806163/200000000000 : ℝ)*(major_s0_2) + (53897771/500000000000 : ℝ)*(sp_s0_0) + (633508063/1000000000000 : ℝ)*(sp_s0_2) + (64770331/250000000000 : ℝ)*(sp_s0_13) + (2218173943/1000000000000 : ℝ)*(sp_s0_20) + (6694304862541/200000000000 : ℝ)*(sp_s0_21) + (1200676477837/31250000000 : ℝ)*(sp_s0_22) + (4183874825023/125000000000 : ℝ)*(sp_s0_23) + (1751527563711/200000000000 : ℝ)*(sp_s0_27) + (342753256409/25000000000 : ℝ)*(f.failure) + (33471632108247/1000000000000 : ℝ)*(f.sum) + (5414265689897/500000000000000000000000000 : ℝ)*base62 + (836722474966313/2000000000000000000000000000 : ℝ)*base65 + (29313307112269/80000000000000000000000000 : ℝ)*base66 + (7575511383731/80000000000000000000000000 : ℝ)*base68 + (342177923813481/1000000000000000000000000000 : ℝ)*base70 + (268596460233687/2000000000000000000000000000 : ℝ)*base73 + (732974997966313/2000000000000000000000000000 : ℝ)*base74 + (5574978247731/80000000000000000000000000 : ℝ)*base76 + (381833147313481/1000000000000000000000000000 : ℝ)*base79 + (2721/2500000000000000 : ℝ)*base87 + (2721/2500000000000000 : ℝ)*base89 + (2721/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (643/6250 : ℝ) ^ (37/8 : ℝ) ≤ (2704149322410381/100000000000000000000 : ℝ) := by
    have hpowers : (643/6250 : ℝ)^37 ≤ (2704149322410381/100000000000000000000 : ℝ)^8 := by
      have hnat : (643 : ℕ)^37*100000000000000000000^8 ≤ 2704149322410381^8*6250^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        643 6250 2704149322410381 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (643/6250 : ℝ)) (X := (2704149322410381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100002704149322410381/100000000000000000000 : ℝ) ≤ (5000029233736931/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (100002704149322410381/100000000000000000000 : ℝ)^8 ≤ (5000029233736931/5000000000000000 : ℝ)^37 := by
      have hnat : (100002704149322410381 : ℕ)^8*5000000000000000^37 ≤ 5000029233736931^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002704149322410381 100000000000000000000 5000029233736931 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029233736931/5000000000000000 : ℝ)) (X := (100002704149322410381/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50002704149322410381/50000000000000000000 : ℝ) ≤ (1000011693370857/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50002704149322410381/50000000000000000000 : ℝ)^8 ≤ (1000011693370857/1000000000000000 : ℝ)^37 := by
      have hnat : (50002704149322410381 : ℕ)^8*1000000000000000^37 ≤ 1000011693370857^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002704149322410381 50000000000000000000 1000011693370857 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000011693370857/1000000000000000 : ℝ)) (X := (50002704149322410381/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29233736931/514400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14616558677/257200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (643/6250 : ℝ)) (alpha := (29233736931/514400000000000 : ℝ)) (beta := (14616558677/257200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (643/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29233736931/514400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14616558677/257200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5719/100000 : ℝ) ^ (37/8 : ℝ) ≤ (35779596799553/20000000000000000000 : ℝ) := by
    have hpowers : (5719/100000 : ℝ)^37 ≤ (35779596799553/20000000000000000000 : ℝ)^8 := by
      have hnat : (5719 : ℕ)^37*20000000000000000000^8 ≤ 35779596799553^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5719 100000 35779596799553 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5719/100000 : ℝ)) (X := (35779596799553/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000035779596799553/20000000000000000000 : ℝ) ≤ (625000241753863/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (20000035779596799553/20000000000000000000 : ℝ)^8 ≤ (625000241753863/625000000000000 : ℝ)^37 := by
      have hnat : (20000035779596799553 : ℕ)^8*625000000000000^37 ≤ 625000241753863^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000035779596799553 20000000000000000000 625000241753863 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000241753863/625000000000000 : ℝ)) (X := (20000035779596799553/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000035779596799553/10000000000000000000 : ℝ) ≤ (10000007736118191/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (10000035779596799553/10000000000000000000 : ℝ)^8 ≤ (10000007736118191/10000000000000000 : ℝ)^37 := by
      have hnat : (10000035779596799553 : ℕ)^8*10000000000000000^37 ≤ 10000007736118191^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000035779596799553 10000000000000000000 10000007736118191 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007736118191/10000000000000000 : ℝ)) (X := (10000035779596799553/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(241753863/35743750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(3868056383/571900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (5719/100000 : ℝ)) (alpha := (241753863/35743750000000 : ℝ)) (beta := (3868056383/571900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (5719/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(241753863/35743750000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(3868056383/571900000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (24531/100000 : ℝ) ^ (37/8 : ℝ) ≤ (150464152292887219/100000000000000000000 : ℝ) := by
    have hpowers : (24531/100000 : ℝ)^37 ≤ (150464152292887219/100000000000000000000 : ℝ)^8 := by
      have hnat : (24531 : ℕ)^37*100000000000000000000^8 ≤ 150464152292887219^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24531 100000 150464152292887219 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24531/100000 : ℝ)) (X := (150464152292887219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100150464152292887219/100000000000000000000 : ℝ) ≤ (5001625681182409/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (100150464152292887219/100000000000000000000 : ℝ)^8 ≤ (5001625681182409/5000000000000000 : ℝ)^37 := by
      have hnat : (100150464152292887219 : ℕ)^8*5000000000000000^37 ≤ 5001625681182409^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100150464152292887219 100000000000000000000 5001625681182409 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001625681182409/5000000000000000 : ℝ)) (X := (100150464152292887219/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50150464152292887219/50000000000000000000 : ℝ) ≤ (125081236229571/125000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50150464152292887219/50000000000000000000 : ℝ)^8 ≤ (125081236229571/125000000000000 : ℝ)^37 := by
      have hnat : (50150464152292887219 : ℕ)^8*125000000000000^37 ≤ 125081236229571^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50150464152292887219 50000000000000000000 125081236229571 125000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125081236229571/125000000000000 : ℝ)) (X := (50150464152292887219/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1625681182409/1226550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1623768000431/1226550000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (24531/100000 : ℝ)) (alpha := (1625681182409/1226550000000000 : ℝ)) (beta := (1623768000431/1226550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (24531/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1625681182409/1226550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1623768000431/1226550000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-803374513/2500000000 : ℝ)*X 0 0+(-5430498823/10000000000 : ℝ)*X 0 1+(3915284497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5210329539/10000000000 : ℝ)*X 1 0+(411963397/1250000000 : ℝ)*X 1 1+(2037736651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3947929713/10000000000 : ℝ)*X 2 0+(-3865731799/10000000000 : ℝ)*X 2 1+(-240505327/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((590917561/1250000000 : ℝ)*X 0 0+(-4199009573/10000000000 : ℝ)*X 0 1+(3697683573/10000000000 : ℝ)*X 0 2+(590917561/1250000000 : ℝ)*X 1 0+(-4199009573/10000000000 : ℝ)*X 1 1+(3697683573/10000000000 : ℝ)*X 1 2+(590917561/1250000000 : ℝ)*X 2 0+(-4199009573/10000000000 : ℝ)*X 2 1+(3697683573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314085_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-216457847848483196121604560967469/30069421109000000000000000000000 : ℝ) := by norm_num
    linear_combination (20439/1000000000000 : ℝ)*(base21) + (323/8000000000 : ℝ)*(base22) + (323/40000000000 : ℝ)*(base39) + (4663694029/12500000000 : ℝ)*(base40) + (110775744563/1000000000000 : ℝ)*(base49) + (5142799351/12500000000 : ℝ)*(base50) + (20297/1000000000000 : ℝ)*(base59) + (23333/1000000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s1_0) + (172069/100000 : ℝ)*(major_s1_1) + (172069/100000 : ℝ)*(major_s1_2) + (1199767293289/500000000000 : ℝ)*(sp_s1_0) + (1199767293289/500000000000 : ℝ)*(sp_s1_1) + (599883631441/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1199767293289/500000000000 : ℝ)*(f.sum) + (20555449651451227/175365986250000000000000000000 : ℝ)*base62 + (2255297984243/122655000000000000000000000 : ℝ)*base64 + (4439329419873/28595000000000000000000000 : ℝ)*base67 + (39454360533599/122655000000000000000000000 : ℝ)*base69 + (3954747418221653/19716791250000000000000000000 : ℝ)*base70 + (601913168123/1607500000000000000000000 : ℝ)*base73 + (2835393140327/14297500000000000000000000 : ℝ)*base74 + (420176744413/1607500000000000000000000 : ℝ)*base76 + (158722385306747/229832312500000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p014_b035 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c314085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
