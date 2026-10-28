-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:02.845275+00:00
-- url     : https://prove2.me/submissions/54f0bf3c-94b6-4085-b281-97b700239cb1

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10082
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c302083
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem collision_support_c302081_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-460681641/1000000000 : ℝ)*x 0 + (1384592473/5000000000 : ℝ)*x 1 + (5547593371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460681641/1000000000 : ℝ)^131 ≤ (8964812412249/25000000000000 : ℝ)^99 := by
    have hnat : (460681641 : ℕ)^131*25000000000000^99 ≤ 8964812412249^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460681641 1000000000 8964812412249 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384592473/5000000000 : ℝ)^131 ≤ (9142650023287/50000000000000 : ℝ)^99 := by
    have hnat : (1384592473 : ℕ)^131*50000000000000^99 ≤ 9142650023287^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384592473 5000000000 9142650023287 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5547593371/10000000000 : ℝ)^131 ≤ (45855450295187/100000000000000 : ℝ)^99 := by
    have hnat : (5547593371 : ℕ)^131*100000000000000^99 ≤ 45855450295187^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547593371 10000000000 45855450295187 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460681641/1000000000 : ℝ), (1384592473/5000000000 : ℝ), (5547593371/10000000000 : ℝ)] ![(8964812412249/25000000000000 : ℝ), (9142650023287/50000000000000 : ℝ), (45855450295187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460681641/1000000000 : ℝ)|^131 ≤ (8964812412249/25000000000000 : ℝ)^99
        have hw : |(-460681641/1000000000 : ℝ)|=(460681641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384592473/5000000000 : ℝ)|^131 ≤ (9142650023287/50000000000000 : ℝ)^99
        have hw : |(1384592473/5000000000 : ℝ)|=(1384592473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5547593371/10000000000 : ℝ)|^131 ≤ (45855450295187/100000000000000 : ℝ)^99
        have hw : |(5547593371/10000000000 : ℝ)|=(5547593371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2105603663/5000000000 : ℝ)*x 0 + (3511020853/5000000000 : ℝ)*x 1 + (-280028693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105603663/5000000000 : ℝ)^131 ≤ (15921086710933/50000000000000 : ℝ)^99 := by
    have hnat : (2105603663 : ℕ)^131*50000000000000^99 ≤ 15921086710933^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105603663 5000000000 15921086710933 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3511020853/5000000000 : ℝ)^131 ≤ (62637643988873/100000000000000 : ℝ)^99 := by
    have hnat : (3511020853 : ℕ)^131*100000000000000^99 ≤ 62637643988873^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511020853 5000000000 62637643988873 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280028693/2500000000 : ℝ)^131 ≤ (27600912871/500000000000 : ℝ)^99 := by
    have hnat : (280028693 : ℕ)^131*500000000000^99 ≤ 27600912871^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280028693 2500000000 27600912871 500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105603663/5000000000 : ℝ), (3511020853/5000000000 : ℝ), (-280028693/2500000000 : ℝ)] ![(15921086710933/50000000000000 : ℝ), (62637643988873/100000000000000 : ℝ), (27600912871/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105603663/5000000000 : ℝ)|^131 ≤ (15921086710933/50000000000000 : ℝ)^99
        have hw : |(2105603663/5000000000 : ℝ)|=(2105603663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3511020853/5000000000 : ℝ)|^131 ≤ (62637643988873/100000000000000 : ℝ)^99
        have hw : |(3511020853/5000000000 : ℝ)|=(3511020853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280028693/2500000000 : ℝ)|^131 ≤ (27600912871/500000000000 : ℝ)^99
        have hw : |(-280028693/2500000000 : ℝ)|=(280028693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3926497/7812500 : ℝ)*x 0 + (1558289221/10000000000 : ℝ)*x 1 + (1206227103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3926497/7812500 : ℝ)^131 ≤ (10059545424193/25000000000000 : ℝ)^99 := by
    have hnat : (3926497 : ℕ)^131*25000000000000^99 ≤ 10059545424193^99*7812500^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926497 7812500 10059545424193 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558289221/10000000000 : ℝ)^131 ≤ (4272241848447/50000000000000 : ℝ)^99 := by
    have hnat : (1558289221 : ℕ)^131*50000000000000^99 ≤ 4272241848447^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558289221 10000000000 4272241848447 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206227103/2000000000 : ℝ)^131 ≤ (51217334587013/100000000000000 : ℝ)^99 := by
    have hnat : (1206227103 : ℕ)^131*100000000000000^99 ≤ 51217334587013^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206227103 2000000000 51217334587013 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3926497/7812500 : ℝ), (1558289221/10000000000 : ℝ), (1206227103/2000000000 : ℝ)] ![(10059545424193/25000000000000 : ℝ), (4272241848447/50000000000000 : ℝ), (51217334587013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3926497/7812500 : ℝ)|^131 ≤ (10059545424193/25000000000000 : ℝ)^99
        have hw : |(-3926497/7812500 : ℝ)|=(3926497/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558289221/10000000000 : ℝ)|^131 ≤ (4272241848447/50000000000000 : ℝ)^99
        have hw : |(1558289221/10000000000 : ℝ)|=(1558289221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206227103/2000000000 : ℝ)|^131 ≤ (51217334587013/100000000000000 : ℝ)^99
        have hw : |(1206227103/2000000000 : ℝ)|=(1206227103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4761000613/10000000000 : ℝ)*x 0 + (-1279016093/5000000000 : ℝ)*x 1 + (1392042243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4761000613/10000000000 : ℝ)^131 ≤ (18727935036871/50000000000000 : ℝ)^99 := by
    have hnat : (4761000613 : ℕ)^131*50000000000000^99 ≤ 18727935036871^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761000613 10000000000 18727935036871 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279016093/5000000000 : ℝ)^131 ≤ (329269938519/2000000000000 : ℝ)^99 := by
    have hnat : (1279016093 : ℕ)^131*2000000000000^99 ≤ 329269938519^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279016093 5000000000 329269938519 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392042243/2500000000 : ℝ)^131 ≤ (1843225319409/4000000000000 : ℝ)^99 := by
    have hnat : (1392042243 : ℕ)^131*4000000000000^99 ≤ 1843225319409^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392042243 2500000000 1843225319409 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4761000613/10000000000 : ℝ), (-1279016093/5000000000 : ℝ), (1392042243/2500000000 : ℝ)] ![(18727935036871/50000000000000 : ℝ), (329269938519/2000000000000 : ℝ), (1843225319409/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4761000613/10000000000 : ℝ)|^131 ≤ (18727935036871/50000000000000 : ℝ)^99
        have hw : |(4761000613/10000000000 : ℝ)|=(4761000613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1279016093/5000000000 : ℝ)|^131 ≤ (329269938519/2000000000000 : ℝ)^99
        have hw : |(-1279016093/5000000000 : ℝ)|=(1279016093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392042243/2500000000 : ℝ)|^131 ≤ (1843225319409/4000000000000 : ℝ)^99
        have hw : |(1392042243/2500000000 : ℝ)|=(1392042243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (632054269/2000000000 : ℝ)*x 0 + (8130970117/10000000000 : ℝ)*x 1 + (-22142197/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (632054269/2000000000 : ℝ)^131 ≤ (21778056502443/100000000000000 : ℝ)^99 := by
    have hnat : (632054269 : ℕ)^131*100000000000000^99 ≤ 21778056502443^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632054269 2000000000 21778056502443 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8130970117/10000000000 : ℝ)^131 ≤ (38024847164421/50000000000000 : ℝ)^99 := by
    have hnat : (8130970117 : ℕ)^131*50000000000000^99 ≤ 38024847164421^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8130970117 10000000000 38024847164421 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22142197/400000000 : ℝ)^131 ≤ (1086124580979/50000000000000 : ℝ)^99 := by
    have hnat : (22142197 : ℕ)^131*50000000000000^99 ≤ 1086124580979^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22142197 400000000 1086124580979 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(632054269/2000000000 : ℝ), (8130970117/10000000000 : ℝ), (-22142197/400000000 : ℝ)] ![(21778056502443/100000000000000 : ℝ), (38024847164421/50000000000000 : ℝ), (1086124580979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(632054269/2000000000 : ℝ)|^131 ≤ (21778056502443/100000000000000 : ℝ)^99
        have hw : |(632054269/2000000000 : ℝ)|=(632054269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8130970117/10000000000 : ℝ)|^131 ≤ (38024847164421/50000000000000 : ℝ)^99
        have hw : |(8130970117/10000000000 : ℝ)|=(8130970117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22142197/400000000 : ℝ)|^131 ≤ (1086124580979/50000000000000 : ℝ)^99
        have hw : |(-22142197/400000000 : ℝ)|=(22142197/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (248633781/2000000000 : ℝ)*x 0 + (5542721667/10000000000 : ℝ)*x 1 + (5730018779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248633781/2000000000 : ℝ)^131 ≤ (6336552126137/100000000000000 : ℝ)^99 := by
    have hnat : (248633781 : ℕ)^131*100000000000000^99 ≤ 6336552126137^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248633781 2000000000 6336552126137 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5542721667/10000000000 : ℝ)^131 ≤ (22901086529821/50000000000000 : ℝ)^99 := by
    have hnat : (5542721667 : ℕ)^131*50000000000000^99 ≤ 22901086529821^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542721667 10000000000 22901086529821 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5730018779/10000000000 : ℝ)^131 ≤ (47861274793443/100000000000000 : ℝ)^99 := by
    have hnat : (5730018779 : ℕ)^131*100000000000000^99 ≤ 47861274793443^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5730018779 10000000000 47861274793443 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(248633781/2000000000 : ℝ), (5542721667/10000000000 : ℝ), (5730018779/10000000000 : ℝ)] ![(6336552126137/100000000000000 : ℝ), (22901086529821/50000000000000 : ℝ), (47861274793443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(248633781/2000000000 : ℝ)|^131 ≤ (6336552126137/100000000000000 : ℝ)^99
        have hw : |(248633781/2000000000 : ℝ)|=(248633781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5542721667/10000000000 : ℝ)|^131 ≤ (22901086529821/50000000000000 : ℝ)^99
        have hw : |(5542721667/10000000000 : ℝ)|=(5542721667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5730018779/10000000000 : ℝ)|^131 ≤ (47861274793443/100000000000000 : ℝ)^99
        have hw : |(5730018779/10000000000 : ℝ)|=(5730018779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4225958433/10000000000 : ℝ)*x 0 + (1611554307/10000000000 : ℝ)*x 1 + (6718241271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225958433/10000000000 : ℝ)^131 ≤ (31989846861489/100000000000000 : ℝ)^99 := by
    have hnat : (4225958433 : ℕ)^131*100000000000000^99 ≤ 31989846861489^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225958433 10000000000 31989846861489 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1611554307/10000000000 : ℝ)^131 ≤ (4466536541627/50000000000000 : ℝ)^99 := by
    have hnat : (1611554307 : ℕ)^131*50000000000000^99 ≤ 4466536541627^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611554307 10000000000 4466536541627 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6718241271/10000000000 : ℝ)^131 ≤ (5907708004731/10000000000000 : ℝ)^99 := by
    have hnat : (6718241271 : ℕ)^131*10000000000000^99 ≤ 5907708004731^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6718241271 10000000000 5907708004731 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4225958433/10000000000 : ℝ), (1611554307/10000000000 : ℝ), (6718241271/10000000000 : ℝ)] ![(31989846861489/100000000000000 : ℝ), (4466536541627/50000000000000 : ℝ), (5907708004731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4225958433/10000000000 : ℝ)|^131 ≤ (31989846861489/100000000000000 : ℝ)^99
        have hw : |(-4225958433/10000000000 : ℝ)|=(4225958433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1611554307/10000000000 : ℝ)|^131 ≤ (4466536541627/50000000000000 : ℝ)^99
        have hw : |(1611554307/10000000000 : ℝ)|=(1611554307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6718241271/10000000000 : ℝ)|^131 ≤ (5907708004731/10000000000000 : ℝ)^99
        have hw : |(6718241271/10000000000 : ℝ)|=(6718241271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (688140319/1250000000 : ℝ)*x 0 + (-3393711559/10000000000 : ℝ)*x 1 + (2047100981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688140319/1250000000 : ℝ)^131 ≤ (22695748391489/50000000000000 : ℝ)^99 := by
    have hnat : (688140319 : ℕ)^131*50000000000000^99 ≤ 22695748391489^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688140319 1250000000 22695748391489 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3393711559/10000000000 : ℝ)^131 ≤ (11965859481779/50000000000000 : ℝ)^99 := by
    have hnat : (3393711559 : ℕ)^131*50000000000000^99 ≤ 11965859481779^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393711559 10000000000 11965859481779 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047100981/5000000000 : ℝ)^131 ≤ (30676784227563/100000000000000 : ℝ)^99 := by
    have hnat : (2047100981 : ℕ)^131*100000000000000^99 ≤ 30676784227563^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047100981 5000000000 30676784227563 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688140319/1250000000 : ℝ), (-3393711559/10000000000 : ℝ), (2047100981/5000000000 : ℝ)] ![(22695748391489/50000000000000 : ℝ), (11965859481779/50000000000000 : ℝ), (30676784227563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688140319/1250000000 : ℝ)|^131 ≤ (22695748391489/50000000000000 : ℝ)^99
        have hw : |(688140319/1250000000 : ℝ)|=(688140319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3393711559/10000000000 : ℝ)|^131 ≤ (11965859481779/50000000000000 : ℝ)^99
        have hw : |(-3393711559/10000000000 : ℝ)|=(3393711559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2047100981/5000000000 : ℝ)|^131 ≤ (30676784227563/100000000000000 : ℝ)^99
        have hw : |(2047100981/5000000000 : ℝ)|=(2047100981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2347082599/5000000000 : ℝ)*x 0 + (1403778511/2000000000 : ℝ)*x 1 + (-109631291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2347082599/5000000000 : ℝ)^131 ≤ (36761685726683/100000000000000 : ℝ)^99 := by
    have hnat : (2347082599 : ℕ)^131*100000000000000^99 ≤ 36761685726683^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347082599 5000000000 36761685726683 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403778511/2000000000 : ℝ)^131 ≤ (6260047590999/10000000000000 : ℝ)^99 := by
    have hnat : (1403778511 : ℕ)^131*10000000000000^99 ≤ 6260047590999^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403778511 2000000000 6260047590999 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109631291/5000000000 : ℝ)^131 ≤ (318919178759/50000000000000 : ℝ)^99 := by
    have hnat : (109631291 : ℕ)^131*50000000000000^99 ≤ 318919178759^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109631291 5000000000 318919178759 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2347082599/5000000000 : ℝ), (1403778511/2000000000 : ℝ), (-109631291/5000000000 : ℝ)] ![(36761685726683/100000000000000 : ℝ), (6260047590999/10000000000000 : ℝ), (318919178759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2347082599/5000000000 : ℝ)|^131 ≤ (36761685726683/100000000000000 : ℝ)^99
        have hw : |(2347082599/5000000000 : ℝ)|=(2347082599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1403778511/2000000000 : ℝ)|^131 ≤ (6260047590999/10000000000000 : ℝ)^99
        have hw : |(1403778511/2000000000 : ℝ)|=(1403778511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109631291/5000000000 : ℝ)|^131 ≤ (318919178759/50000000000000 : ℝ)^99
        have hw : |(-109631291/5000000000 : ℝ)|=(109631291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1222966679/10000000000 : ℝ)*x 0 + (1478029377/5000000000 : ℝ)*x 1 + (7953714789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222966679/10000000000 : ℝ)^131 ≤ (3100327250867/50000000000000 : ℝ)^99 := by
    have hnat : (1222966679 : ℕ)^131*50000000000000^99 ≤ 3100327250867^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222966679 10000000000 3100327250867 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1478029377/5000000000 : ℝ)^131 ≤ (9967825337119/50000000000000 : ℝ)^99 := by
    have hnat : (1478029377 : ℕ)^131*50000000000000^99 ≤ 9967825337119^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478029377 5000000000 9967825337119 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7953714789/10000000000 : ℝ)^131 ≤ (73863694810169/100000000000000 : ℝ)^99 := by
    have hnat : (7953714789 : ℕ)^131*100000000000000^99 ≤ 73863694810169^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7953714789 10000000000 73863694810169 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1222966679/10000000000 : ℝ), (1478029377/5000000000 : ℝ), (7953714789/10000000000 : ℝ)] ![(3100327250867/50000000000000 : ℝ), (9967825337119/50000000000000 : ℝ), (73863694810169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1222966679/10000000000 : ℝ)|^131 ≤ (3100327250867/50000000000000 : ℝ)^99
        have hw : |(1222966679/10000000000 : ℝ)|=(1222966679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1478029377/5000000000 : ℝ)|^131 ≤ (9967825337119/50000000000000 : ℝ)^99
        have hw : |(1478029377/5000000000 : ℝ)|=(1478029377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7953714789/10000000000 : ℝ)|^131 ≤ (73863694810169/100000000000000 : ℝ)^99
        have hw : |(7953714789/10000000000 : ℝ)|=(7953714789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5648696709/10000000000 : ℝ)*x 0 + (824117607/5000000000 : ℝ)*x 1 + (2680806237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5648696709/10000000000 : ℝ)^131 ≤ (11741130757169/25000000000000 : ℝ)^99 := by
    have hnat : (5648696709 : ℕ)^131*25000000000000^99 ≤ 11741130757169^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648696709 10000000000 11741130757169 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824117607/5000000000 : ℝ)^131 ≤ (4601553609313/50000000000000 : ℝ)^99 := by
    have hnat : (824117607 : ℕ)^131*50000000000000^99 ≤ 4601553609313^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824117607 5000000000 4601553609313 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2680806237/5000000000 : ℝ)^131 ≤ (43832369742763/100000000000000 : ℝ)^99 := by
    have hnat : (2680806237 : ℕ)^131*100000000000000^99 ≤ 43832369742763^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680806237 5000000000 43832369742763 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5648696709/10000000000 : ℝ), (824117607/5000000000 : ℝ), (2680806237/5000000000 : ℝ)] ![(11741130757169/25000000000000 : ℝ), (4601553609313/50000000000000 : ℝ), (43832369742763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5648696709/10000000000 : ℝ)|^131 ≤ (11741130757169/25000000000000 : ℝ)^99
        have hw : |(-5648696709/10000000000 : ℝ)|=(5648696709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824117607/5000000000 : ℝ)|^131 ≤ (4601553609313/50000000000000 : ℝ)^99
        have hw : |(824117607/5000000000 : ℝ)|=(824117607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2680806237/5000000000 : ℝ)|^131 ≤ (43832369742763/100000000000000 : ℝ)^99
        have hw : |(2680806237/5000000000 : ℝ)|=(2680806237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (459650987/1250000000 : ℝ)*x 0 + (-4473488651/10000000000 : ℝ)*x 1 + (2449322769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459650987/1250000000 : ℝ)^131 ≤ (26612128829987/100000000000000 : ℝ)^99 := by
    have hnat : (459650987 : ℕ)^131*100000000000000^99 ≤ 26612128829987^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459650987 1250000000 26612128829987 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473488651/10000000000 : ℝ)^131 ≤ (6898488432193/20000000000000 : ℝ)^99 := by
    have hnat : (4473488651 : ℕ)^131*20000000000000^99 ≤ 6898488432193^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473488651 10000000000 6898488432193 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2449322769/5000000000 : ℝ)^131 ≤ (1944771449533/5000000000000 : ℝ)^99 := by
    have hnat : (2449322769 : ℕ)^131*5000000000000^99 ≤ 1944771449533^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449322769 5000000000 1944771449533 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(459650987/1250000000 : ℝ), (-4473488651/10000000000 : ℝ), (2449322769/5000000000 : ℝ)] ![(26612128829987/100000000000000 : ℝ), (6898488432193/20000000000000 : ℝ), (1944771449533/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(459650987/1250000000 : ℝ)|^131 ≤ (26612128829987/100000000000000 : ℝ)^99
        have hw : |(459650987/1250000000 : ℝ)|=(459650987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4473488651/10000000000 : ℝ)|^131 ≤ (6898488432193/20000000000000 : ℝ)^99
        have hw : |(-4473488651/10000000000 : ℝ)|=(4473488651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2449322769/5000000000 : ℝ)|^131 ≤ (1944771449533/5000000000000 : ℝ)^99
        have hw : |(2449322769/5000000000 : ℝ)|=(2449322769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5200243637/10000000000 : ℝ)*x 0 + (157771457/250000000 : ℝ)*x 1 + (-12458913/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200243637/10000000000 : ℝ)^131 ≤ (42095276767823/100000000000000 : ℝ)^99 := by
    have hnat : (5200243637 : ℕ)^131*100000000000000^99 ≤ 42095276767823^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200243637 10000000000 42095276767823 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157771457/250000000 : ℝ)^131 ≤ (3398995290713/6250000000000 : ℝ)^99 := by
    have hnat : (157771457 : ℕ)^131*6250000000000^99 ≤ 3398995290713^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157771457 250000000 3398995290713 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12458913/156250000 : ℝ)^131 ≤ (704159712717/20000000000000 : ℝ)^99 := by
    have hnat : (12458913 : ℕ)^131*20000000000000^99 ≤ 704159712717^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12458913 156250000 704159712717 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200243637/10000000000 : ℝ), (157771457/250000000 : ℝ), (-12458913/156250000 : ℝ)] ![(42095276767823/100000000000000 : ℝ), (3398995290713/6250000000000 : ℝ), (704159712717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200243637/10000000000 : ℝ)|^131 ≤ (42095276767823/100000000000000 : ℝ)^99
        have hw : |(5200243637/10000000000 : ℝ)|=(5200243637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157771457/250000000 : ℝ)|^131 ≤ (3398995290713/6250000000000 : ℝ)^99
        have hw : |(157771457/250000000 : ℝ)|=(157771457/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12458913/156250000 : ℝ)|^131 ≤ (704159712717/20000000000000 : ℝ)^99
        have hw : |(-12458913/156250000 : ℝ)|=(12458913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s0_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (127854659/1250000000 : ℝ)*x 0 + (2587608151/5000000000 : ℝ)*x 1 + (1553400597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127854659/1250000000 : ℝ)^131 ≤ (2447451074023/50000000000000 : ℝ)^99 := by
    have hnat : (127854659 : ℕ)^131*50000000000000^99 ≤ 2447451074023^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127854659 1250000000 2447451074023 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587608151/5000000000 : ℝ)^131 ≤ (20913703998021/50000000000000 : ℝ)^99 := by
    have hnat : (2587608151 : ℕ)^131*50000000000000^99 ≤ 20913703998021^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587608151 5000000000 20913703998021 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1553400597/2500000000 : ℝ)^131 ≤ (53277689836527/100000000000000 : ℝ)^99 := by
    have hnat : (1553400597 : ℕ)^131*100000000000000^99 ≤ 53277689836527^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553400597 2500000000 53277689836527 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127854659/1250000000 : ℝ), (2587608151/5000000000 : ℝ), (1553400597/2500000000 : ℝ)] ![(2447451074023/50000000000000 : ℝ), (20913703998021/50000000000000 : ℝ), (53277689836527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127854659/1250000000 : ℝ)|^131 ≤ (2447451074023/50000000000000 : ℝ)^99
        have hw : |(127854659/1250000000 : ℝ)|=(127854659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587608151/5000000000 : ℝ)|^131 ≤ (20913703998021/50000000000000 : ℝ)^99
        have hw : |(2587608151/5000000000 : ℝ)|=(2587608151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1553400597/2500000000 : ℝ)|^131 ≤ (53277689836527/100000000000000 : ℝ)^99
        have hw : |(1553400597/2500000000 : ℝ)|=(1553400597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2242711899/5000000000 : ℝ)*x 0 + (3625775321/10000000000 : ℝ)*x 1 + (4933782459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242711899/5000000000 : ℝ)^131 ≤ (34614264963927/100000000000000 : ℝ)^99 := by
    have hnat : (2242711899 : ℕ)^131*100000000000000^99 ≤ 34614264963927^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242711899 5000000000 34614264963927 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3625775321/10000000000 : ℝ)^131 ≤ (13060356102679/50000000000000 : ℝ)^99 := by
    have hnat : (3625775321 : ℕ)^131*50000000000000^99 ≤ 13060356102679^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3625775321 10000000000 13060356102679 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4933782459/10000000000 : ℝ)^131 ≤ (7853004562237/20000000000000 : ℝ)^99 := by
    have hnat : (4933782459 : ℕ)^131*20000000000000^99 ≤ 7853004562237^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933782459 10000000000 7853004562237 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2242711899/5000000000 : ℝ), (3625775321/10000000000 : ℝ), (4933782459/10000000000 : ℝ)] ![(34614264963927/100000000000000 : ℝ), (13060356102679/50000000000000 : ℝ), (7853004562237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2242711899/5000000000 : ℝ)|^131 ≤ (34614264963927/100000000000000 : ℝ)^99
        have hw : |(-2242711899/5000000000 : ℝ)|=(2242711899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3625775321/10000000000 : ℝ)|^131 ≤ (13060356102679/50000000000000 : ℝ)^99
        have hw : |(3625775321/10000000000 : ℝ)|=(3625775321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4933782459/10000000000 : ℝ)|^131 ≤ (7853004562237/20000000000000 : ℝ)^99
        have hw : |(4933782459/10000000000 : ℝ)|=(4933782459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4610127683/10000000000 : ℝ)*x 0 + (-3726579233/10000000000 : ℝ)*x 1 + (117978451/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4610127683/10000000000 : ℝ)^131 ≤ (717867193139/2000000000000 : ℝ)^99 := by
    have hnat : (4610127683 : ℕ)^131*2000000000000^99 ≤ 717867193139^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610127683 10000000000 717867193139 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726579233/10000000000 : ℝ)^131 ≤ (423217908881/1562500000000 : ℝ)^99 := by
    have hnat : (3726579233 : ℕ)^131*1562500000000^99 ≤ 423217908881^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726579233 10000000000 423217908881 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117978451/250000000 : ℝ)^131 ≤ (37020694166451/100000000000000 : ℝ)^99 := by
    have hnat : (117978451 : ℕ)^131*100000000000000^99 ≤ 37020694166451^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117978451 250000000 37020694166451 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4610127683/10000000000 : ℝ), (-3726579233/10000000000 : ℝ), (117978451/250000000 : ℝ)] ![(717867193139/2000000000000 : ℝ), (423217908881/1562500000000 : ℝ), (37020694166451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4610127683/10000000000 : ℝ)|^131 ≤ (717867193139/2000000000000 : ℝ)^99
        have hw : |(4610127683/10000000000 : ℝ)|=(4610127683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3726579233/10000000000 : ℝ)|^131 ≤ (423217908881/1562500000000 : ℝ)^99
        have hw : |(-3726579233/10000000000 : ℝ)|=(3726579233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117978451/250000000 : ℝ)|^131 ≤ (37020694166451/100000000000000 : ℝ)^99
        have hw : |(117978451/250000000 : ℝ)|=(117978451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4444259123/10000000000 : ℝ)*x 0 + (2855628227/5000000000 : ℝ)*x 1 + (-275385207/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444259123/10000000000 : ℝ)^131 ≤ (34194538406733/100000000000000 : ℝ)^99 := by
    have hnat : (4444259123 : ℕ)^131*100000000000000^99 ≤ 34194538406733^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444259123 10000000000 34194538406733 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2855628227/5000000000 : ℝ)^131 ≤ (23827006103123/50000000000000 : ℝ)^99 := by
    have hnat : (2855628227 : ℕ)^131*50000000000000^99 ≤ 23827006103123^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855628227 5000000000 23827006103123 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275385207/1000000000 : ℝ)^131 ≤ (18151449373717/100000000000000 : ℝ)^99 := by
    have hnat : (275385207 : ℕ)^131*100000000000000^99 ≤ 18151449373717^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275385207 1000000000 18151449373717 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444259123/10000000000 : ℝ), (2855628227/5000000000 : ℝ), (-275385207/1000000000 : ℝ)] ![(34194538406733/100000000000000 : ℝ), (23827006103123/50000000000000 : ℝ), (18151449373717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444259123/10000000000 : ℝ)|^131 ≤ (34194538406733/100000000000000 : ℝ)^99
        have hw : |(4444259123/10000000000 : ℝ)|=(4444259123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2855628227/5000000000 : ℝ)|^131 ≤ (23827006103123/50000000000000 : ℝ)^99
        have hw : |(2855628227/5000000000 : ℝ)|=(2855628227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275385207/1000000000 : ℝ)|^131 ≤ (18151449373717/100000000000000 : ℝ)^99
        have hw : |(-275385207/1000000000 : ℝ)|=(275385207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302081_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1638190483/5000000000 : ℝ)*x 0 + (16841729/40000000 : ℝ)*x 1 + (687349977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1638190483/5000000000 : ℝ)^131 ≤ (11421527842581/50000000000000 : ℝ)^99 := by
    have hnat : (1638190483 : ℕ)^131*50000000000000^99 ≤ 11421527842581^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638190483 5000000000 11421527842581 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16841729/40000000 : ℝ)^131 ≤ (31834418747753/100000000000000 : ℝ)^99 := by
    have hnat : (16841729 : ℕ)^131*100000000000000^99 ≤ 31834418747753^99*40000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16841729 40000000 31834418747753 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687349977/1250000000 : ℝ)^131 ≤ (22661262772579/50000000000000 : ℝ)^99 := by
    have hnat : (687349977 : ℕ)^131*50000000000000^99 ≤ 22661262772579^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687349977 1250000000 22661262772579 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1638190483/5000000000 : ℝ), (16841729/40000000 : ℝ), (687349977/1250000000 : ℝ)] ![(11421527842581/50000000000000 : ℝ), (31834418747753/100000000000000 : ℝ), (22661262772579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1638190483/5000000000 : ℝ)|^131 ≤ (11421527842581/50000000000000 : ℝ)^99
        have hw : |(1638190483/5000000000 : ℝ)|=(1638190483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16841729/40000000 : ℝ)|^131 ≤ (31834418747753/100000000000000 : ℝ)^99
        have hw : |(16841729/40000000 : ℝ)|=(16841729/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687349977/1250000000 : ℝ)|^131 ≤ (22661262772579/50000000000000 : ℝ)^99
        have hw : |(687349977/1250000000 : ℝ)|=(687349977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302081 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-460681641/1000000000 : ℝ)*X 0 0+(1384592473/5000000000 : ℝ)*X 0 1+(5547593371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2105603663/5000000000 : ℝ)*X 2 0+(3511020853/5000000000 : ℝ)*X 2 1+(-280028693/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3926497/7812500 : ℝ)*X 0 0+(1558289221/10000000000 : ℝ)*X 0 1+(1206227103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4761000613/10000000000 : ℝ)*X 1 0+(-1279016093/5000000000 : ℝ)*X 1 1+(1392042243/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((632054269/2000000000 : ℝ)*X 2 0+(8130970117/10000000000 : ℝ)*X 2 1+(-22142197/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((248633781/2000000000 : ℝ)*X 0 0+(5542721667/10000000000 : ℝ)*X 0 1+(5730018779/10000000000 : ℝ)*X 0 2+(248633781/2000000000 : ℝ)*X 1 0+(5542721667/10000000000 : ℝ)*X 1 1+(5730018779/10000000000 : ℝ)*X 1 2+(248633781/2000000000 : ℝ)*X 2 0+(5542721667/10000000000 : ℝ)*X 2 1+(5730018779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4225958433/10000000000 : ℝ)*X 0 0+(1611554307/10000000000 : ℝ)*X 0 1+(6718241271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((688140319/1250000000 : ℝ)*X 1 0+(-3393711559/10000000000 : ℝ)*X 1 1+(2047100981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2347082599/5000000000 : ℝ)*X 2 0+(1403778511/2000000000 : ℝ)*X 2 1+(-109631291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1222966679/10000000000 : ℝ)*X 0 0+(1478029377/5000000000 : ℝ)*X 0 1+(7953714789/10000000000 : ℝ)*X 0 2+(1222966679/10000000000 : ℝ)*X 1 0+(1478029377/5000000000 : ℝ)*X 1 1+(7953714789/10000000000 : ℝ)*X 1 2+(1222966679/10000000000 : ℝ)*X 2 0+(1478029377/5000000000 : ℝ)*X 2 1+(7953714789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5648696709/10000000000 : ℝ)*X 0 0+(824117607/5000000000 : ℝ)*X 0 1+(2680806237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((459650987/1250000000 : ℝ)*X 1 0+(-4473488651/10000000000 : ℝ)*X 1 1+(2449322769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((5200243637/10000000000 : ℝ)*X 2 0+(157771457/250000000 : ℝ)*X 2 1+(-12458913/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((127854659/1250000000 : ℝ)*X 0 0+(2587608151/5000000000 : ℝ)*X 0 1+(1553400597/2500000000 : ℝ)*X 0 2+(127854659/1250000000 : ℝ)*X 1 0+(2587608151/5000000000 : ℝ)*X 1 1+(1553400597/2500000000 : ℝ)*X 1 2+(127854659/1250000000 : ℝ)*X 2 0+(2587608151/5000000000 : ℝ)*X 2 1+(1553400597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((36599/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36599/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13249332537048760759707/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1029072966593/1000000000000 : ℝ)*(base49) + (278230703207/250000000000 : ℝ)*(base59) + (750076486797/200000000000 : ℝ)*(major_s0_0) + (750076486797/200000000000 : ℝ)*(major_s0_1) + (750076486797/200000000000 : ℝ)*(major_s0_2) + (98732709/1000000000000 : ℝ)*(sp_s0_0) + (65484631/1000000000000 : ℝ)*(sp_s0_2) + (623304552893/125000000000 : ℝ)*(sp_s0_7) + (2493288764089/500000000000 : ℝ)*(sp_s0_8) + (4986528288611/1000000000000 : ℝ)*(sp_s0_9) + (502819038547/200000000000 : ℝ)*(sp_s0_13) + (58617389/1000000000000 : ℝ)*(sp_s0_14) + (3249013/200000000000 : ℝ)*(sp_s0_22) + (35742771/500000000000 : ℝ)*(sp_s0_27) + (628541669569/250000000000 : ℝ)*(f.failure) + (2493296886621/500000000000 : ℝ)*(f.sum) + (4880742246351/100000000000000000000000000 : ℝ)*base62 + (474842660213589/2000000000000000000000000000 : ℝ)*base64 + (216803780513431/2000000000000000000000000000 : ℝ)*base67 + (336637866913431/2000000000000000000000000000 : ℝ)*base68 + (256648853550079/1000000000000000000000000000 : ℝ)*base70 + (1006172687186411/2000000000000000000000000000 : ℝ)*base72 + (1012874097786411/2000000000000000000000000000 : ℝ)*base75 + (338620695913431/2000000000000000000000000000 : ℝ)*base77 + (36855157613649/100000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1727/2500000000000000 : ℝ)*base86 + (1727/2500000000000000 : ℝ)*base88 + (1727/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((5279/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5279/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (74667560203750511160381/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39022248361/200000000000 : ℝ)*(base40) + (2201581573/3125000000 : ℝ)*(base49) + (300743329689/200000000000 : ℝ)*(base59) + (4965469/1000000000000 : ℝ)*(base60) + (4159237605671/1000000000000 : ℝ)*(major_s0_0) + (4159237605671/1000000000000 : ℝ)*(major_s0_1) + (4159237605671/1000000000000 : ℝ)*(major_s0_2) + (60029817/1000000000000 : ℝ)*(sp_s0_7) + (2950603/100000000000 : ℝ)*(sp_s0_8) + (2765078398861/500000000000 : ℝ)*(sp_s0_14) + (5530187321509/1000000000000 : ℝ)*(sp_s0_15) + (5530126214169/1000000000000 : ℝ)*(sp_s0_16) + (2788253405961/1000000000000 : ℝ)*(sp_s0_20) + (9061337/100000000000 : ℝ)*(sp_s0_23) + (2788253405961/1000000000000 : ℝ)*(f.failure) + (5530216827539/1000000000000 : ℝ)*(f.sum) + (360270160215293/500000000000000000000000000 : ℝ)*base62 + (426804118279873/10000000000000000000000000000 : ℝ)*base65 + (5744402691414267/10000000000000000000000000000 : ℝ)*base66 + (3439630831585733/10000000000000000000000000000 : ℝ)*base68 + (232994697432803/5000000000000000000000000000 : ℝ)*base71 + (4775186970279873/10000000000000000000000000000 : ℝ)*base72 + (6203662747720127/10000000000000000000000000000 : ℝ)*base74 + (4513758034414267/10000000000000000000000000000 : ℝ)*base76 + (175949749984707/500000000000000000000000000 : ℝ)*base78 + (10237/10000000000000000 : ℝ)*base87 + (10237/10000000000000000 : ℝ)*base89 + (10237/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2759/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2759/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34786216088879119763283/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2179643/500000000000 : ℝ)*(base40) + (450410253409/1000000000000 : ℝ)*(base49) + (603271025071/500000000000 : ℝ)*(base59) + (3899281672507/1000000000000 : ℝ)*(major_s0_0) + (3899281672507/1000000000000 : ℝ)*(major_s0_1) + (3899281672507/1000000000000 : ℝ)*(major_s0_2) + (32606851/1000000000000 : ℝ)*(sp_s0_0) + (137601249/1000000000000 : ℝ)*(sp_s0_13) + (97109/2000000000 : ℝ)*(sp_s0_15) + (8362081/250000000000 : ℝ)*(sp_s0_16) + (5184540933739/1000000000000 : ℝ)*(sp_s0_21) + (5184524986089/1000000000000 : ℝ)*(sp_s0_22) + (1036908018453/200000000000 : ℝ)*(sp_s0_23) + (2613847565009/1000000000000 : ℝ)*(sp_s0_27) + (1306992583129/500000000000 : ℝ)*(f.failure) + (5184573540589/1000000000000 : ℝ)*(f.sum) + (285782576713719/500000000000000000000000000 : ℝ)*base63 + (4053864350112141/10000000000000000000000000000 : ℝ)*base65 + (1786227593162239/10000000000000000000000000000 : ℝ)*base66 + (3601865586162239/10000000000000000000000000000 : ℝ)*base69 + (1501115071025049/5000000000000000000000000000 : ℝ)*base70 + (7892500311887859/10000000000000000000000000000 : ℝ)*base73 + (7254579593112141/10000000000000000000000000000 : ℝ)*base75 + (668256944162239/10000000000000000000000000000 : ℝ)*base76 + (199349255936281/500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (293/5000000000000000 : ℝ)*base87 + (293/5000000000000000 : ℝ)*base89 + (293/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (36599/100000 : ℝ) ^ (65/16 : ℝ) ≤ (1684975937491807657/100000000000000000000 : ℝ) := by
    have hpowers : (36599/100000 : ℝ)^65 ≤ (1684975937491807657/100000000000000000000 : ℝ)^16 := by
      have hnat : (36599 : ℕ)^65*100000000000000000000^16 ≤ 1684975937491807657^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36599 100000 1684975937491807657 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36599/100000 : ℝ)) (X := (1684975937491807657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101684975937491807657/100000000000000000000 : ℝ) ≤ (2008243095417679/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (101684975937491807657/100000000000000000000 : ℝ)^16 ≤ (2008243095417679/2000000000000000 : ℝ)^65 := by
      have hnat : (101684975937491807657 : ℕ)^16*2000000000000000^65 ≤ 2008243095417679^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101684975937491807657 100000000000000000000 2008243095417679 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008243095417679/2000000000000000 : ℝ)) (X := (101684975937491807657/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51684975937491807657/50000000000000000000 : ℝ) ≤ (100819192753293/100000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (51684975937491807657/50000000000000000000 : ℝ)^16 ≤ (100819192753293/100000000000000 : ℝ)^65 := by
      have hnat : (51684975937491807657 : ℕ)^16*100000000000000^65 ≤ 100819192753293^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51684975937491807657 50000000000000000000 100819192753293 100000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100819192753293/100000000000000 : ℝ)) (X := (51684975937491807657/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8243095417679/731980000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8140759648181/731980000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (36599/100000 : ℝ)) (alpha := (8243095417679/731980000000000 : ℝ)) (beta := (8140759648181/731980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36599/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8243095417679/731980000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8140759648181/731980000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5279/12500 : ℝ) ^ (65/16 : ℝ) ≤ (3014180105481706457/100000000000000000000 : ℝ) := by
    have hpowers : (5279/12500 : ℝ)^65 ≤ (3014180105481706457/100000000000000000000 : ℝ)^16 := by
      have hnat : (5279 : ℕ)^65*100000000000000000000^16 ≤ 3014180105481706457^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5279 12500 3014180105481706457 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5279/12500 : ℝ)) (X := (3014180105481706457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (103014180105481706457/100000000000000000000 : ℝ) ≤ (10073366812844709/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (103014180105481706457/100000000000000000000 : ℝ)^16 ≤ (10073366812844709/10000000000000000 : ℝ)^65 := by
      have hnat : (103014180105481706457 : ℕ)^16*10000000000000000^65 ≤ 10073366812844709^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103014180105481706457 100000000000000000000 10073366812844709 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073366812844709/10000000000000000 : ℝ)) (X := (103014180105481706457/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53014180105481706457/50000000000000000000 : ℝ) ≤ (10145132748278289/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (53014180105481706457/50000000000000000000 : ℝ)^16 ≤ (10145132748278289/10000000000000000 : ℝ)^65 := by
      have hnat : (53014180105481706457 : ℕ)^16*10000000000000000^65 ≤ 10145132748278289^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53014180105481706457 50000000000000000000 10145132748278289 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10145132748278289/10000000000000000 : ℝ)) (X := (53014180105481706457/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(73366812844709/4223200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(3588296771679/211160000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5279/12500 : ℝ)) (alpha := (73366812844709/4223200000000000 : ℝ)) (beta := (3588296771679/211160000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (5279/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(73366812844709/4223200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(3588296771679/211160000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2759/12500 : ℝ) ^ (65/16 : ℝ) ≤ (107975906718905249/50000000000000000000 : ℝ) := by
    have hpowers : (2759/12500 : ℝ)^65 ≤ (107975906718905249/50000000000000000000 : ℝ)^16 := by
      have hnat : (2759 : ℕ)^65*50000000000000000000^16 ≤ 107975906718905249^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 12500 107975906718905249 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/12500 : ℝ)) (X := (107975906718905249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50107975906718905249/50000000000000000000 : ℝ) ≤ (10005311415538461/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50107975906718905249/50000000000000000000 : ℝ)^16 ≤ (10005311415538461/10000000000000000 : ℝ)^65 := by
      have hnat : (50107975906718905249 : ℕ)^16*10000000000000000^65 ≤ 10005311415538461^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50107975906718905249 50000000000000000000 10005311415538461 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005311415538461/10000000000000000 : ℝ)) (X := (50107975906718905249/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25107975906718905249/25000000000000000000 : ℝ) ≤ (5005307105007433/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25107975906718905249/25000000000000000000 : ℝ)^16 ≤ (5005307105007433/5000000000000000 : ℝ)^65 := by
      have hnat : (25107975906718905249 : ℕ)^16*5000000000000000^65 ≤ 5005307105007433^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25107975906718905249 25000000000000000000 5005307105007433 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005307105007433/5000000000000000 : ℝ)) (X := (25107975906718905249/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5311415538461/2207200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1060558895281/441440000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (2759/12500 : ℝ)) (alpha := (5311415538461/2207200000000000 : ℝ)) (beta := (1060558895281/441440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2759/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5311415538461/2207200000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1060558895281/441440000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2242711899/5000000000 : ℝ)*X 0 0+(3625775321/10000000000 : ℝ)*X 0 1+(4933782459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4610127683/10000000000 : ℝ)*X 1 0+(-3726579233/10000000000 : ℝ)*X 1 1+(117978451/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4444259123/10000000000 : ℝ)*X 2 0+(2855628227/5000000000 : ℝ)*X 2 1+(-275385207/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1638190483/5000000000 : ℝ)*X 0 0+(16841729/40000000 : ℝ)*X 0 1+(687349977/1250000000 : ℝ)*X 0 2+(1638190483/5000000000 : ℝ)*X 1 0+(16841729/40000000 : ℝ)*X 1 1+(687349977/1250000000 : ℝ)*X 1 2+(1638190483/5000000000 : ℝ)*X 2 0+(16841729/40000000 : ℝ)*X 2 1+(687349977/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302081_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-50591616718390335793937615216589/8597672384500000000000000000000 : ℝ) := by norm_num
    linear_combination (389591/500000000000 : ℝ)*(base8) + (364213/200000000000 : ℝ)*(base15) + (512949/500000000000 : ℝ)*(base23) + (46759/125000000000 : ℝ)*(base29) + (32777554659/1000000000000 : ℝ)*(base40) + (33374512233/125000000000 : ℝ)*(base49) + (306058170343/500000000000 : ℝ)*(base59) + (256219646531/1000000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s1_0) + (14917/10000 : ℝ)*(major_s1_1) + (14917/10000 : ℝ)*(major_s1_2) + (98072273437/50000000000 : ℝ)*(sp_s1_0) + (1961444426857/1000000000000 : ℝ)*(sp_s1_1) + (245180652753/125000000000 : ℝ)*(sp_s1_2) + (124999953241/125000000000 : ℝ)*(sp_s1_6) + (980723123961/500000000000 : ℝ)*(f.sum) + (8317757552802401/18205951250000000000000000000 : ℝ)*base62 + (508185846157/1379500000000000000000000 : ℝ)*base65 + (3397567429167/13197500000000000000000000 : ℝ)*base67 + (1667803411261/27590000000000000000000000 : ℝ)*base68 + (717200694145104521/1009766410000000000000000000000 : ℝ)*base71 + (8237596644409/45748750000000000000000000 : ℝ)*base72 + (44646486903/263950000000000000000000 : ℝ)*base74 + (22747955451/89353027343750000000000 : ℝ)*base77 + (15443349287757679/60376912812500000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c302084_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-267535377/625000000 : ℝ)*x 0 + (-5370121191/10000000000 : ℝ)*x 1 + (3351388017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267535377/625000000 : ℝ)^131 ≤ (32537971761457/100000000000000 : ℝ)^99 := by
    have hnat : (267535377 : ℕ)^131*100000000000000^99 ≤ 32537971761457^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267535377 625000000 32537971761457 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5370121191/10000000000 : ℝ)^131 ≤ (21962219118883/50000000000000 : ℝ)^99 := by
    have hnat : (5370121191 : ℕ)^131*50000000000000^99 ≤ 21962219118883^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370121191 10000000000 21962219118883 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3351388017/10000000000 : ℝ)^131 ≤ (941503599287/4000000000000 : ℝ)^99 := by
    have hnat : (3351388017 : ℕ)^131*4000000000000^99 ≤ 941503599287^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351388017 10000000000 941503599287 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267535377/625000000 : ℝ), (-5370121191/10000000000 : ℝ), (3351388017/10000000000 : ℝ)] ![(32537971761457/100000000000000 : ℝ), (21962219118883/50000000000000 : ℝ), (941503599287/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267535377/625000000 : ℝ)|^131 ≤ (32537971761457/100000000000000 : ℝ)^99
        have hw : |(-267535377/625000000 : ℝ)|=(267535377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5370121191/10000000000 : ℝ)|^131 ≤ (21962219118883/50000000000000 : ℝ)^99
        have hw : |(-5370121191/10000000000 : ℝ)|=(5370121191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3351388017/10000000000 : ℝ)|^131 ≤ (941503599287/4000000000000 : ℝ)^99
        have hw : |(3351388017/10000000000 : ℝ)|=(3351388017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302084_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3351388017/10000000000 : ℝ)*x 0 + (267535377/625000000 : ℝ)*x 1 + (5370121191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3351388017/10000000000 : ℝ)^131 ≤ (941503599287/4000000000000 : ℝ)^99 := by
    have hnat : (3351388017 : ℕ)^131*4000000000000^99 ≤ 941503599287^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351388017 10000000000 941503599287 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267535377/625000000 : ℝ)^131 ≤ (32537971761457/100000000000000 : ℝ)^99 := by
    have hnat : (267535377 : ℕ)^131*100000000000000^99 ≤ 32537971761457^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267535377 625000000 32537971761457 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5370121191/10000000000 : ℝ)^131 ≤ (21962219118883/50000000000000 : ℝ)^99 := by
    have hnat : (5370121191 : ℕ)^131*50000000000000^99 ≤ 21962219118883^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370121191 10000000000 21962219118883 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3351388017/10000000000 : ℝ), (267535377/625000000 : ℝ), (5370121191/10000000000 : ℝ)] ![(941503599287/4000000000000 : ℝ), (32537971761457/100000000000000 : ℝ), (21962219118883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3351388017/10000000000 : ℝ)|^131 ≤ (941503599287/4000000000000 : ℝ)^99
        have hw : |(3351388017/10000000000 : ℝ)|=(3351388017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(267535377/625000000 : ℝ)|^131 ≤ (32537971761457/100000000000000 : ℝ)^99
        have hw : |(267535377/625000000 : ℝ)|=(267535377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5370121191/10000000000 : ℝ)|^131 ≤ (21962219118883/50000000000000 : ℝ)^99
        have hw : |(5370121191/10000000000 : ℝ)|=(5370121191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302084_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5370121191/10000000000 : ℝ)*x 0 + (-3351388017/10000000000 : ℝ)*x 1 + (-267535377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370121191/10000000000 : ℝ)^131 ≤ (21962219118883/50000000000000 : ℝ)^99 := by
    have hnat : (5370121191 : ℕ)^131*50000000000000^99 ≤ 21962219118883^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370121191 10000000000 21962219118883 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3351388017/10000000000 : ℝ)^131 ≤ (941503599287/4000000000000 : ℝ)^99 := by
    have hnat : (3351388017 : ℕ)^131*4000000000000^99 ≤ 941503599287^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351388017 10000000000 941503599287 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267535377/625000000 : ℝ)^131 ≤ (32537971761457/100000000000000 : ℝ)^99 := by
    have hnat : (267535377 : ℕ)^131*100000000000000^99 ≤ 32537971761457^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267535377 625000000 32537971761457 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370121191/10000000000 : ℝ), (-3351388017/10000000000 : ℝ), (-267535377/625000000 : ℝ)] ![(21962219118883/50000000000000 : ℝ), (941503599287/4000000000000 : ℝ), (32537971761457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370121191/10000000000 : ℝ)|^131 ≤ (21962219118883/50000000000000 : ℝ)^99
        have hw : |(5370121191/10000000000 : ℝ)|=(5370121191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3351388017/10000000000 : ℝ)|^131 ≤ (941503599287/4000000000000 : ℝ)^99
        have hw : |(-3351388017/10000000000 : ℝ)|=(3351388017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267535377/625000000 : ℝ)|^131 ≤ (32537971761457/100000000000000 : ℝ)^99
        have hw : |(-267535377/625000000 : ℝ)|=(267535377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302084 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-267535377/625000000 : ℝ)*X 0 0+(-5370121191/10000000000 : ℝ)*X 0 1+(3351388017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302084_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3351388017/10000000000 : ℝ)*X 1 0+(267535377/625000000 : ℝ)*X 1 1+(5370121191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302084_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5370121191/10000000000 : ℝ)*X 2 0+(-3351388017/10000000000 : ℝ)*X 2 1+(-267535377/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302084_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-29418351833134329459333/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (257/500000000000 : ℝ)*(base1) + (17/200000000000 : ℝ)*(base3) + (999999999111/1000000000000 : ℝ)*(base6) + (29/100000000000 : ℝ)*(base27) + (22259383653/50000000000 : ℝ)*(base40) + (222593836493/500000000000 : ℝ)*(base50) + (89037534573/200000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s0_0) + (14917/10000 : ℝ)*(major_s0_1) + (14917/10000 : ℝ)*(major_s0_2) + (2294556788279/1000000000000 : ℝ)*(sp_s0_0) + (91782271511/40000000000 : ℝ)*(sp_s0_1) + (1147278394029/500000000000 : ℝ)*(sp_s0_2) + (229455678769/100000000000 : ℝ)*(f.sum) + (661565341/1250000000000000000000 : ℝ)*base63 + (753491317389/10000000000000000000000 : ℝ)*base65 + (2475728157/10000000000000000000000 : ℝ)*base67 + (63011549/400000000000000000000 : ℝ)*base69 + (39436213/50000000000000000000 : ℝ)*base70 + (24398103/80000000000000000000 : ℝ)*base73 + (1838347267089/5000000000000000000000 : ℝ)*base74 + (1566239957/5000000000000000000000 : ℝ)*base76 + (1160928707/1250000000000000000000 : ℝ)*base79 + (3/40000000000 : ℝ)*base81 + (23/62500000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b035 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=81 ∨ c=82 ∨ c=83 ∨ c=84 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c302081 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10082 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c302083 p hpa (by linarith only [hpb]) X hX
  · exact collision_c302084 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 81 ≤ c.val) (hhi : c.val < 85)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
