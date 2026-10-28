-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b035
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:55:01.827256+00:00
-- url     : https://prove2.me/submissions/ae907a9b-0c69-4255-857c-d395fe5bc31d

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10080
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
theorem collision_support_c303079_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8155316989/10000000000 : ℝ)*x 0 + (-770202241/5000000000 : ℝ)*x 1 + (-2391774579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8155316989/10000000000 : ℝ)^33 ≤ (76401505610869/100000000000000 : ℝ)^25 := by
    have hnat : (8155316989 : ℕ)^33*100000000000000^25 ≤ 76401505610869^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8155316989 10000000000 76401505610869 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770202241/5000000000 : ℝ)^33 ≤ (8465992923729/100000000000000 : ℝ)^25 := by
    have hnat : (770202241 : ℕ)^33*100000000000000^25 ≤ 8465992923729^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770202241 5000000000 8465992923729 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391774579/10000000000 : ℝ)^33 ≤ (15132501453069/100000000000000 : ℝ)^25 := by
    have hnat : (2391774579 : ℕ)^33*100000000000000^25 ≤ 15132501453069^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391774579 10000000000 15132501453069 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8155316989/10000000000 : ℝ), (-770202241/5000000000 : ℝ), (-2391774579/10000000000 : ℝ)] ![(76401505610869/100000000000000 : ℝ), (8465992923729/100000000000000 : ℝ), (15132501453069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8155316989/10000000000 : ℝ)|^33 ≤ (76401505610869/100000000000000 : ℝ)^25
        have hw : |(8155316989/10000000000 : ℝ)|=(8155316989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-770202241/5000000000 : ℝ)|^33 ≤ (8465992923729/100000000000000 : ℝ)^25
        have hw : |(-770202241/5000000000 : ℝ)|=(770202241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2391774579/10000000000 : ℝ)|^33 ≤ (15132501453069/100000000000000 : ℝ)^25
        have hw : |(-2391774579/10000000000 : ℝ)|=(2391774579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (162976617/500000000 : ℝ)*x 0 + (3031348789/5000000000 : ℝ)*x 1 + (3559295313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162976617/500000000 : ℝ)^33 ≤ (22770102652237/100000000000000 : ℝ)^25 := by
    have hnat : (162976617 : ℕ)^33*100000000000000^25 ≤ 22770102652237^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162976617 500000000 22770102652237 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3031348789/5000000000 : ℝ)^33 ≤ (5165578844451/10000000000000 : ℝ)^25 := by
    have hnat : (3031348789 : ℕ)^33*10000000000000^25 ≤ 5165578844451^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031348789 5000000000 5165578844451 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3559295313/10000000000 : ℝ)^33 ≤ (12787054444161/50000000000000 : ℝ)^25 := by
    have hnat : (3559295313 : ℕ)^33*50000000000000^25 ≤ 12787054444161^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3559295313 10000000000 12787054444161 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162976617/500000000 : ℝ), (3031348789/5000000000 : ℝ), (3559295313/10000000000 : ℝ)] ![(22770102652237/100000000000000 : ℝ), (5165578844451/10000000000000 : ℝ), (12787054444161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162976617/500000000 : ℝ)|^33 ≤ (22770102652237/100000000000000 : ℝ)^25
        have hw : |(162976617/500000000 : ℝ)|=(162976617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3031348789/5000000000 : ℝ)|^33 ≤ (5165578844451/10000000000000 : ℝ)^25
        have hw : |(3031348789/5000000000 : ℝ)|=(3031348789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3559295313/10000000000 : ℝ)|^33 ≤ (12787054444161/50000000000000 : ℝ)^25
        have hw : |(3559295313/10000000000 : ℝ)|=(3559295313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (872998949/2500000000 : ℝ)*x 0 + (5320312839/10000000000 : ℝ)*x 1 + (-2088405867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872998949/2500000000 : ℝ)^33 ≤ (12468875954639/50000000000000 : ℝ)^25 := by
    have hnat : (872998949 : ℕ)^33*50000000000000^25 ≤ 12468875954639^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872998949 2500000000 12468875954639 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5320312839/10000000000 : ℝ)^33 ≤ (8694949420001/20000000000000 : ℝ)^25 := by
    have hnat : (5320312839 : ℕ)^33*20000000000000^25 ≤ 8694949420001^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5320312839 10000000000 8694949420001 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088405867/5000000000 : ℝ)^33 ≤ (3158750097731/10000000000000 : ℝ)^25 := by
    have hnat : (2088405867 : ℕ)^33*10000000000000^25 ≤ 3158750097731^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088405867 5000000000 3158750097731 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872998949/2500000000 : ℝ), (5320312839/10000000000 : ℝ), (-2088405867/5000000000 : ℝ)] ![(12468875954639/50000000000000 : ℝ), (8694949420001/20000000000000 : ℝ), (3158750097731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872998949/2500000000 : ℝ)|^33 ≤ (12468875954639/50000000000000 : ℝ)^25
        have hw : |(872998949/2500000000 : ℝ)|=(872998949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5320312839/10000000000 : ℝ)|^33 ≤ (8694949420001/20000000000000 : ℝ)^25
        have hw : |(5320312839/10000000000 : ℝ)|=(5320312839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088405867/5000000000 : ℝ)|^33 ≤ (3158750097731/10000000000000 : ℝ)^25
        have hw : |(-2088405867/5000000000 : ℝ)|=(2088405867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1685993047/10000000000 : ℝ)*x 0 + (364020217/1250000000 : ℝ)*x 1 + (-385071171/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1685993047/10000000000 : ℝ)^33 ≤ (9537831125139/100000000000000 : ℝ)^25 := by
    have hnat : (1685993047 : ℕ)^33*100000000000000^25 ≤ 9537831125139^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685993047 10000000000 9537831125139 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364020217/1250000000 : ℝ)^33 ≤ (78491827317/400000000000 : ℝ)^25 := by
    have hnat : (364020217 : ℕ)^33*400000000000^25 ≤ 78491827317^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364020217 1250000000 78491827317 400000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385071171/500000000 : ℝ)^33 ≤ (17709803007837/25000000000000 : ℝ)^25 := by
    have hnat : (385071171 : ℕ)^33*25000000000000^25 ≤ 17709803007837^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385071171 500000000 17709803007837 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1685993047/10000000000 : ℝ), (364020217/1250000000 : ℝ), (-385071171/500000000 : ℝ)] ![(9537831125139/100000000000000 : ℝ), (78491827317/400000000000 : ℝ), (17709803007837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1685993047/10000000000 : ℝ)|^33 ≤ (9537831125139/100000000000000 : ℝ)^25
        have hw : |(-1685993047/10000000000 : ℝ)|=(1685993047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364020217/1250000000 : ℝ)|^33 ≤ (78491827317/400000000000 : ℝ)^25
        have hw : |(364020217/1250000000 : ℝ)|=(364020217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385071171/500000000 : ℝ)|^33 ≤ (17709803007837/25000000000000 : ℝ)^25
        have hw : |(-385071171/500000000 : ℝ)|=(385071171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2017994579/2500000000 : ℝ)*x 0 + (-279845451/10000000000 : ℝ)*x 1 + (-3363780747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017994579/2500000000 : ℝ)^33 ≤ (75372614861069/100000000000000 : ℝ)^25 := by
    have hnat : (2017994579 : ℕ)^33*100000000000000^25 ≤ 75372614861069^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017994579 2500000000 75372614861069 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279845451/10000000000 : ℝ)^33 ≤ (891111589931/100000000000000 : ℝ)^25 := by
    have hnat : (279845451 : ℕ)^33*100000000000000^25 ≤ 891111589931^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279845451 10000000000 891111589931 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3363780747/10000000000 : ℝ)^33 ≤ (23736273543371/100000000000000 : ℝ)^25 := by
    have hnat : (3363780747 : ℕ)^33*100000000000000^25 ≤ 23736273543371^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3363780747 10000000000 23736273543371 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2017994579/2500000000 : ℝ), (-279845451/10000000000 : ℝ), (-3363780747/10000000000 : ℝ)] ![(75372614861069/100000000000000 : ℝ), (891111589931/100000000000000 : ℝ), (23736273543371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2017994579/2500000000 : ℝ)|^33 ≤ (75372614861069/100000000000000 : ℝ)^25
        have hw : |(2017994579/2500000000 : ℝ)|=(2017994579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279845451/10000000000 : ℝ)|^33 ≤ (891111589931/100000000000000 : ℝ)^25
        have hw : |(-279845451/10000000000 : ℝ)|=(279845451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3363780747/10000000000 : ℝ)|^33 ≤ (23736273543371/100000000000000 : ℝ)^25
        have hw : |(-3363780747/10000000000 : ℝ)|=(3363780747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (70983107/500000000 : ℝ)*x 0 + (7981371501/10000000000 : ℝ)*x 1 + (137198157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70983107/500000000 : ℝ)^33 ≤ (3800617862061/50000000000000 : ℝ)^25 := by
    have hnat : (70983107 : ℕ)^33*50000000000000^25 ≤ 3800617862061^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70983107 500000000 3800617862061 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7981371501/10000000000 : ℝ)^33 ≤ (9282230467501/12500000000000 : ℝ)^25 := by
    have hnat : (7981371501 : ℕ)^33*12500000000000^25 ≤ 9282230467501^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7981371501 10000000000 9282230467501 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137198157/500000000 : ℝ)^33 ≤ (4535230129711/25000000000000 : ℝ)^25 := by
    have hnat : (137198157 : ℕ)^33*25000000000000^25 ≤ 4535230129711^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137198157 500000000 4535230129711 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70983107/500000000 : ℝ), (7981371501/10000000000 : ℝ), (137198157/500000000 : ℝ)] ![(3800617862061/50000000000000 : ℝ), (9282230467501/12500000000000 : ℝ), (4535230129711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70983107/500000000 : ℝ)|^33 ≤ (3800617862061/50000000000000 : ℝ)^25
        have hw : |(70983107/500000000 : ℝ)|=(70983107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7981371501/10000000000 : ℝ)|^33 ≤ (9282230467501/12500000000000 : ℝ)^25
        have hw : |(7981371501/10000000000 : ℝ)|=(7981371501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137198157/500000000 : ℝ)|^33 ≤ (4535230129711/25000000000000 : ℝ)^25
        have hw : |(137198157/500000000 : ℝ)|=(137198157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2385815853/10000000000 : ℝ)*x 0 + (3821693103/5000000000 : ℝ)*x 1 + (-234966833/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2385815853/10000000000 : ℝ)^33 ≤ (1508275700953/10000000000000 : ℝ)^25 := by
    have hnat : (2385815853 : ℕ)^33*10000000000000^25 ≤ 1508275700953^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385815853 10000000000 1508275700953 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3821693103/5000000000 : ℝ)^33 ≤ (35067698655957/50000000000000 : ℝ)^25 := by
    have hnat : (3821693103 : ℕ)^33*50000000000000^25 ≤ 35067698655957^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821693103 5000000000 35067698655957 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234966833/1000000000 : ℝ)^33 ≤ (1478184566411/10000000000000 : ℝ)^25 := by
    have hnat : (234966833 : ℕ)^33*10000000000000^25 ≤ 1478184566411^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234966833 1000000000 1478184566411 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2385815853/10000000000 : ℝ), (3821693103/5000000000 : ℝ), (-234966833/1000000000 : ℝ)] ![(1508275700953/10000000000000 : ℝ), (35067698655957/50000000000000 : ℝ), (1478184566411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2385815853/10000000000 : ℝ)|^33 ≤ (1508275700953/10000000000000 : ℝ)^25
        have hw : |(2385815853/10000000000 : ℝ)|=(2385815853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3821693103/5000000000 : ℝ)|^33 ≤ (35067698655957/50000000000000 : ℝ)^25
        have hw : |(3821693103/5000000000 : ℝ)|=(3821693103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234966833/1000000000 : ℝ)|^33 ≤ (1478184566411/10000000000000 : ℝ)^25
        have hw : |(-234966833/1000000000 : ℝ)|=(234966833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-146665399/5000000000 : ℝ)*x 0 + (3580525007/10000000000 : ℝ)*x 1 + (-3950652659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146665399/5000000000 : ℝ)^33 ≤ (189645312131/20000000000000 : ℝ)^25 := by
    have hnat : (146665399 : ℕ)^33*20000000000000^25 ≤ 189645312131^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146665399 5000000000 189645312131 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3580525007/10000000000 : ℝ)^33 ≤ (25775651952973/100000000000000 : ℝ)^25 := by
    have hnat : (3580525007 : ℕ)^33*100000000000000^25 ≤ 25775651952973^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3580525007 10000000000 25775651952973 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3950652659/5000000000 : ℝ)^33 ≤ (73276121474671/100000000000000 : ℝ)^25 := by
    have hnat : (3950652659 : ℕ)^33*100000000000000^25 ≤ 73276121474671^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3950652659 5000000000 73276121474671 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-146665399/5000000000 : ℝ), (3580525007/10000000000 : ℝ), (-3950652659/5000000000 : ℝ)] ![(189645312131/20000000000000 : ℝ), (25775651952973/100000000000000 : ℝ), (73276121474671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-146665399/5000000000 : ℝ)|^33 ≤ (189645312131/20000000000000 : ℝ)^25
        have hw : |(-146665399/5000000000 : ℝ)|=(146665399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3580525007/10000000000 : ℝ)|^33 ≤ (25775651952973/100000000000000 : ℝ)^25
        have hw : |(3580525007/10000000000 : ℝ)|=(3580525007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3950652659/5000000000 : ℝ)|^33 ≤ (73276121474671/100000000000000 : ℝ)^25
        have hw : |(-3950652659/5000000000 : ℝ)|=(3950652659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (374114781/400000000 : ℝ)*x 0 + (-1135494037/10000000000 : ℝ)*x 1 + (-166188589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374114781/400000000 : ℝ)^33 ≤ (18309531499463/20000000000000 : ℝ)^25 := by
    have hnat : (374114781 : ℕ)^33*20000000000000^25 ≤ 18309531499463^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374114781 400000000 18309531499463 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135494037/10000000000 : ℝ)^33 ≤ (2830179733623/50000000000000 : ℝ)^25 := by
    have hnat : (1135494037 : ℕ)^33*50000000000000^25 ≤ 2830179733623^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135494037 10000000000 2830179733623 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166188589/2500000000 : ℝ)^33 ≤ (697995755867/25000000000000 : ℝ)^25 := by
    have hnat : (166188589 : ℕ)^33*25000000000000^25 ≤ 697995755867^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166188589 2500000000 697995755867 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(374114781/400000000 : ℝ), (-1135494037/10000000000 : ℝ), (-166188589/2500000000 : ℝ)] ![(18309531499463/20000000000000 : ℝ), (2830179733623/50000000000000 : ℝ), (697995755867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(374114781/400000000 : ℝ)|^33 ≤ (18309531499463/20000000000000 : ℝ)^25
        have hw : |(374114781/400000000 : ℝ)|=(374114781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135494037/10000000000 : ℝ)|^33 ≤ (2830179733623/50000000000000 : ℝ)^25
        have hw : |(-1135494037/10000000000 : ℝ)|=(1135494037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166188589/2500000000 : ℝ)|^33 ≤ (697995755867/25000000000000 : ℝ)^25
        have hw : |(-166188589/2500000000 : ℝ)|=(166188589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (798059511/2000000000 : ℝ)*x 0 + (2931395939/5000000000 : ℝ)*x 1 + (3048156241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798059511/2000000000 : ℝ)^33 ≤ (29739041869127/100000000000000 : ℝ)^25 := by
    have hnat : (798059511 : ℕ)^33*100000000000000^25 ≤ 29739041869127^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798059511 2000000000 29739041869127 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2931395939/5000000000 : ℝ)^33 ≤ (49419450296723/100000000000000 : ℝ)^25 := by
    have hnat : (2931395939 : ℕ)^33*100000000000000^25 ≤ 49419450296723^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931395939 5000000000 49419450296723 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3048156241/10000000000 : ℝ)^33 ≤ (20841507827921/100000000000000 : ℝ)^25 := by
    have hnat : (3048156241 : ℕ)^33*100000000000000^25 ≤ 20841507827921^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048156241 10000000000 20841507827921 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(798059511/2000000000 : ℝ), (2931395939/5000000000 : ℝ), (3048156241/10000000000 : ℝ)] ![(29739041869127/100000000000000 : ℝ), (49419450296723/100000000000000 : ℝ), (20841507827921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(798059511/2000000000 : ℝ)|^33 ≤ (29739041869127/100000000000000 : ℝ)^25
        have hw : |(798059511/2000000000 : ℝ)|=(798059511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2931395939/5000000000 : ℝ)|^33 ≤ (49419450296723/100000000000000 : ℝ)^25
        have hw : |(2931395939/5000000000 : ℝ)|=(2931395939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3048156241/10000000000 : ℝ)|^33 ≤ (20841507827921/100000000000000 : ℝ)^25
        have hw : |(3048156241/10000000000 : ℝ)|=(3048156241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2696455661/10000000000 : ℝ)*x 0 + (811808997/2500000000 : ℝ)*x 1 + (-422375631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696455661/10000000000 : ℝ)^33 ≤ (17727485306223/100000000000000 : ℝ)^25 := by
    have hnat : (2696455661 : ℕ)^33*100000000000000^25 ≤ 17727485306223^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696455661 10000000000 17727485306223 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811808997/2500000000 : ℝ)^33 ≤ (22656785024699/100000000000000 : ℝ)^25 := by
    have hnat : (811808997 : ℕ)^33*100000000000000^25 ≤ 22656785024699^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811808997 2500000000 22656785024699 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422375631/625000000 : ℝ)^33 ≤ (59615729663073/100000000000000 : ℝ)^25 := by
    have hnat : (422375631 : ℕ)^33*100000000000000^25 ≤ 59615729663073^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422375631 625000000 59615729663073 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696455661/10000000000 : ℝ), (811808997/2500000000 : ℝ), (-422375631/625000000 : ℝ)] ![(17727485306223/100000000000000 : ℝ), (22656785024699/100000000000000 : ℝ), (59615729663073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696455661/10000000000 : ℝ)|^33 ≤ (17727485306223/100000000000000 : ℝ)^25
        have hw : |(2696455661/10000000000 : ℝ)|=(2696455661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(811808997/2500000000 : ℝ)|^33 ≤ (22656785024699/100000000000000 : ℝ)^25
        have hw : |(811808997/2500000000 : ℝ)|=(811808997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422375631/625000000 : ℝ)|^33 ≤ (59615729663073/100000000000000 : ℝ)^25
        have hw : |(-422375631/625000000 : ℝ)|=(422375631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-441620449/10000000000 : ℝ)*x 0 + (5772375899/10000000000 : ℝ)*x 1 + (-2955511171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441620449/10000000000 : ℝ)^33 ≤ (325457966519/20000000000000 : ℝ)^25 := by
    have hnat : (441620449 : ℕ)^33*20000000000000^25 ≤ 325457966519^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441620449 10000000000 325457966519 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5772375899/10000000000 : ℝ)^33 ≤ (1512997115109/3125000000000 : ℝ)^25 := by
    have hnat : (5772375899 : ℕ)^33*3125000000000^25 ≤ 1512997115109^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5772375899 10000000000 1512997115109 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2955511171/5000000000 : ℝ)^33 ≤ (4995680246489/10000000000000 : ℝ)^25 := by
    have hnat : (2955511171 : ℕ)^33*10000000000000^25 ≤ 4995680246489^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955511171 5000000000 4995680246489 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441620449/10000000000 : ℝ), (5772375899/10000000000 : ℝ), (-2955511171/5000000000 : ℝ)] ![(325457966519/20000000000000 : ℝ), (1512997115109/3125000000000 : ℝ), (4995680246489/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441620449/10000000000 : ℝ)|^33 ≤ (325457966519/20000000000000 : ℝ)^25
        have hw : |(-441620449/10000000000 : ℝ)|=(441620449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5772375899/10000000000 : ℝ)|^33 ≤ (1512997115109/3125000000000 : ℝ)^25
        have hw : |(5772375899/10000000000 : ℝ)|=(5772375899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2955511171/5000000000 : ℝ)|^33 ≤ (4995680246489/10000000000000 : ℝ)^25
        have hw : |(-2955511171/5000000000 : ℝ)|=(2955511171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (603940259/625000000 : ℝ)*x 0 + (-83841981/2500000000 : ℝ)*x 1 + (-23535309/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603940259/625000000 : ℝ)^33 ≤ (95576347977229/100000000000000 : ℝ)^25 := by
    have hnat : (603940259 : ℕ)^33*100000000000000^25 ≤ 95576347977229^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603940259 625000000 95576347977229 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83841981/2500000000 : ℝ)^33 ≤ (282897049767/25000000000000 : ℝ)^25 := by
    have hnat : (83841981 : ℕ)^33*25000000000000^25 ≤ 282897049767^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83841981 2500000000 282897049767 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23535309/312500000 : ℝ)^33 ≤ (3292063817147/100000000000000 : ℝ)^25 := by
    have hnat : (23535309 : ℕ)^33*100000000000000^25 ≤ 3292063817147^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23535309 312500000 3292063817147 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(603940259/625000000 : ℝ), (-83841981/2500000000 : ℝ), (-23535309/312500000 : ℝ)] ![(95576347977229/100000000000000 : ℝ), (282897049767/25000000000000 : ℝ), (3292063817147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(603940259/625000000 : ℝ)|^33 ≤ (95576347977229/100000000000000 : ℝ)^25
        have hw : |(603940259/625000000 : ℝ)|=(603940259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83841981/2500000000 : ℝ)|^33 ≤ (282897049767/25000000000000 : ℝ)^25
        have hw : |(-83841981/2500000000 : ℝ)|=(83841981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23535309/312500000 : ℝ)|^33 ≤ (3292063817147/100000000000000 : ℝ)^25
        have hw : |(-23535309/312500000 : ℝ)|=(23535309/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1310523953/5000000000 : ℝ)*x 0 + (1557632031/2500000000 : ℝ)*x 1 + (988241223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310523953/5000000000 : ℝ)^33 ≤ (2134503929381/12500000000000 : ℝ)^25 := by
    have hnat : (1310523953 : ℕ)^33*12500000000000^25 ≤ 2134503929381^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310523953 5000000000 2134503929381 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557632031/2500000000 : ℝ)^33 ≤ (53551645014689/100000000000000 : ℝ)^25 := by
    have hnat : (1557632031 : ℕ)^33*100000000000000^25 ≤ 53551645014689^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557632031 2500000000 53551645014689 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988241223/2500000000 : ℝ)^33 ≤ (14686161774523/50000000000000 : ℝ)^25 := by
    have hnat : (988241223 : ℕ)^33*50000000000000^25 ≤ 14686161774523^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988241223 2500000000 14686161774523 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310523953/5000000000 : ℝ), (1557632031/2500000000 : ℝ), (988241223/2500000000 : ℝ)] ![(2134503929381/12500000000000 : ℝ), (53551645014689/100000000000000 : ℝ), (14686161774523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310523953/5000000000 : ℝ)|^33 ≤ (2134503929381/12500000000000 : ℝ)^25
        have hw : |(1310523953/5000000000 : ℝ)|=(1310523953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1557632031/2500000000 : ℝ)|^33 ≤ (53551645014689/100000000000000 : ℝ)^25
        have hw : |(1557632031/2500000000 : ℝ)|=(1557632031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(988241223/2500000000 : ℝ)|^33 ≤ (14686161774523/50000000000000 : ℝ)^25
        have hw : |(988241223/2500000000 : ℝ)|=(988241223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s0_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4525679289/10000000000 : ℝ)*x 0 + (1060762869/2000000000 : ℝ)*x 1 + (-3130438103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4525679289/10000000000 : ℝ)^33 ≤ (219473757857/625000000000 : ℝ)^25 := by
    have hnat : (4525679289 : ℕ)^33*625000000000^25 ≤ 219473757857^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525679289 10000000000 219473757857 625000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060762869/2000000000 : ℝ)^33 ≤ (43296877208023/100000000000000 : ℝ)^25 := by
    have hnat : (1060762869 : ℕ)^33*100000000000000^25 ≤ 43296877208023^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060762869 2000000000 43296877208023 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3130438103/10000000000 : ℝ)^33 ≤ (4317464302779/20000000000000 : ℝ)^25 := by
    have hnat : (3130438103 : ℕ)^33*20000000000000^25 ≤ 4317464302779^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3130438103 10000000000 4317464302779 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4525679289/10000000000 : ℝ), (1060762869/2000000000 : ℝ), (-3130438103/10000000000 : ℝ)] ![(219473757857/625000000000 : ℝ), (43296877208023/100000000000000 : ℝ), (4317464302779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4525679289/10000000000 : ℝ)|^33 ≤ (219473757857/625000000000 : ℝ)^25
        have hw : |(4525679289/10000000000 : ℝ)|=(4525679289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060762869/2000000000 : ℝ)|^33 ≤ (43296877208023/100000000000000 : ℝ)^25
        have hw : |(1060762869/2000000000 : ℝ)|=(1060762869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3130438103/10000000000 : ℝ)|^33 ≤ (4317464302779/20000000000000 : ℝ)^25
        have hw : |(-3130438103/10000000000 : ℝ)|=(3130438103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-670372601/2500000000 : ℝ)*x 0 + (4483151589/10000000000 : ℝ)*x 1 + (-2854768009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670372601/2500000000 : ℝ)^33 ≤ (8798864921621/50000000000000 : ℝ)^25 := by
    have hnat : (670372601 : ℕ)^33*50000000000000^25 ≤ 8798864921621^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670372601 2500000000 8798864921621 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483151589/10000000000 : ℝ)^33 ≤ (433511010747/1250000000000 : ℝ)^25 := by
    have hnat : (4483151589 : ℕ)^33*1250000000000^25 ≤ 433511010747^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483151589 10000000000 433511010747 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2854768009/5000000000 : ℝ)^33 ≤ (23860694636809/50000000000000 : ℝ)^25 := by
    have hnat : (2854768009 : ℕ)^33*50000000000000^25 ≤ 23860694636809^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854768009 5000000000 23860694636809 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-670372601/2500000000 : ℝ), (4483151589/10000000000 : ℝ), (-2854768009/5000000000 : ℝ)] ![(8798864921621/50000000000000 : ℝ), (433511010747/1250000000000 : ℝ), (23860694636809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-670372601/2500000000 : ℝ)|^33 ≤ (8798864921621/50000000000000 : ℝ)^25
        have hw : |(-670372601/2500000000 : ℝ)|=(670372601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483151589/10000000000 : ℝ)|^33 ≤ (433511010747/1250000000000 : ℝ)^25
        have hw : |(4483151589/10000000000 : ℝ)|=(4483151589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2854768009/5000000000 : ℝ)|^33 ≤ (23860694636809/50000000000000 : ℝ)^25
        have hw : |(-2854768009/5000000000 : ℝ)|=(2854768009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3262611703/5000000000 : ℝ)*x 0 + (-90456989/312500000 : ℝ)*x 1 + (-670102233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3262611703/5000000000 : ℝ)^33 ≤ (7115016665151/12500000000000 : ℝ)^25 := by
    have hnat : (3262611703 : ℕ)^33*12500000000000^25 ≤ 7115016665151^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3262611703 5000000000 7115016665151 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90456989/312500000 : ℝ)^33 ≤ (19467114338101/100000000000000 : ℝ)^25 := by
    have hnat : (90456989 : ℕ)^33*100000000000000^25 ≤ 19467114338101^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90456989 312500000 19467114338101 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670102233/2000000000 : ℝ)^33 ≤ (11806376160099/50000000000000 : ℝ)^25 := by
    have hnat : (670102233 : ℕ)^33*50000000000000^25 ≤ 11806376160099^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670102233 2000000000 11806376160099 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3262611703/5000000000 : ℝ), (-90456989/312500000 : ℝ), (-670102233/2000000000 : ℝ)] ![(7115016665151/12500000000000 : ℝ), (19467114338101/100000000000000 : ℝ), (11806376160099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3262611703/5000000000 : ℝ)|^33 ≤ (7115016665151/12500000000000 : ℝ)^25
        have hw : |(3262611703/5000000000 : ℝ)|=(3262611703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90456989/312500000 : ℝ)|^33 ≤ (19467114338101/100000000000000 : ℝ)^25
        have hw : |(-90456989/312500000 : ℝ)|=(90456989/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-670102233/2000000000 : ℝ)|^33 ≤ (11806376160099/50000000000000 : ℝ)^25
        have hw : |(-670102233/2000000000 : ℝ)|=(670102233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (245162319/625000000 : ℝ)*x 0 + (5236173207/10000000000 : ℝ)*x 1 + (3848870147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245162319/625000000 : ℝ)^33 ≤ (29074836985577/100000000000000 : ℝ)^25 := by
    have hnat : (245162319 : ℕ)^33*100000000000000^25 ≤ 29074836985577^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245162319 625000000 29074836985577 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236173207/10000000000 : ℝ)^33 ≤ (21284746874471/50000000000000 : ℝ)^25 := by
    have hnat : (5236173207 : ℕ)^33*50000000000000^25 ≤ 21284746874471^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236173207 10000000000 21284746874471 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3848870147/10000000000 : ℝ)^33 ≤ (14177834628413/50000000000000 : ℝ)^25 := by
    have hnat : (3848870147 : ℕ)^33*50000000000000^25 ≤ 14177834628413^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848870147 10000000000 14177834628413 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(245162319/625000000 : ℝ), (5236173207/10000000000 : ℝ), (3848870147/10000000000 : ℝ)] ![(29074836985577/100000000000000 : ℝ), (21284746874471/50000000000000 : ℝ), (14177834628413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(245162319/625000000 : ℝ)|^33 ≤ (29074836985577/100000000000000 : ℝ)^25
        have hw : |(245162319/625000000 : ℝ)|=(245162319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236173207/10000000000 : ℝ)|^33 ≤ (21284746874471/50000000000000 : ℝ)^25
        have hw : |(5236173207/10000000000 : ℝ)|=(5236173207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3848870147/10000000000 : ℝ)|^33 ≤ (14177834628413/50000000000000 : ℝ)^25
        have hw : |(3848870147/10000000000 : ℝ)|=(3848870147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303079_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (481756249/1250000000 : ℝ)*x 0 + (2441824863/5000000000 : ℝ)*x 1 + (-536794497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481756249/1250000000 : ℝ)^33 ≤ (1420302652243/5000000000000 : ℝ)^25 := by
    have hnat : (481756249 : ℕ)^33*5000000000000^25 ≤ 1420302652243^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481756249 1250000000 1420302652243 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441824863/5000000000 : ℝ)^33 ≤ (38827796914187/100000000000000 : ℝ)^25 := by
    have hnat : (2441824863 : ℕ)^33*100000000000000^25 ≤ 38827796914187^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441824863 5000000000 38827796914187 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536794497/1250000000 : ℝ)^33 ≤ (32766150023739/100000000000000 : ℝ)^25 := by
    have hnat : (536794497 : ℕ)^33*100000000000000^25 ≤ 32766150023739^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536794497 1250000000 32766150023739 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(481756249/1250000000 : ℝ), (2441824863/5000000000 : ℝ), (-536794497/1250000000 : ℝ)] ![(1420302652243/5000000000000 : ℝ), (38827796914187/100000000000000 : ℝ), (32766150023739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(481756249/1250000000 : ℝ)|^33 ≤ (1420302652243/5000000000000 : ℝ)^25
        have hw : |(481756249/1250000000 : ℝ)|=(481756249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2441824863/5000000000 : ℝ)|^33 ≤ (38827796914187/100000000000000 : ℝ)^25
        have hw : |(2441824863/5000000000 : ℝ)|=(2441824863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536794497/1250000000 : ℝ)|^33 ≤ (32766150023739/100000000000000 : ℝ)^25
        have hw : |(-536794497/1250000000 : ℝ)|=(536794497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303079 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((8155316989/10000000000 : ℝ)*X 1 0+(-770202241/5000000000 : ℝ)*X 1 1+(-2391774579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((162976617/500000000 : ℝ)*X 2 0+(3031348789/5000000000 : ℝ)*X 2 1+(3559295313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((872998949/2500000000 : ℝ)*X 0 0+(5320312839/10000000000 : ℝ)*X 0 1+(-2088405867/5000000000 : ℝ)*X 0 2+(872998949/2500000000 : ℝ)*X 1 0+(5320312839/10000000000 : ℝ)*X 1 1+(-2088405867/5000000000 : ℝ)*X 1 2+(872998949/2500000000 : ℝ)*X 2 0+(5320312839/10000000000 : ℝ)*X 2 1+(-2088405867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1685993047/10000000000 : ℝ)*X 0 0+(364020217/1250000000 : ℝ)*X 0 1+(-385071171/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2017994579/2500000000 : ℝ)*X 1 0+(-279845451/10000000000 : ℝ)*X 1 1+(-3363780747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((70983107/500000000 : ℝ)*X 2 0+(7981371501/10000000000 : ℝ)*X 2 1+(137198157/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2385815853/10000000000 : ℝ)*X 0 0+(3821693103/5000000000 : ℝ)*X 0 1+(-234966833/1000000000 : ℝ)*X 0 2+(2385815853/10000000000 : ℝ)*X 1 0+(3821693103/5000000000 : ℝ)*X 1 1+(-234966833/1000000000 : ℝ)*X 1 2+(2385815853/10000000000 : ℝ)*X 2 0+(3821693103/5000000000 : ℝ)*X 2 1+(-234966833/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-146665399/5000000000 : ℝ)*X 0 0+(3580525007/10000000000 : ℝ)*X 0 1+(-3950652659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((374114781/400000000 : ℝ)*X 1 0+(-1135494037/10000000000 : ℝ)*X 1 1+(-166188589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((798059511/2000000000 : ℝ)*X 2 0+(2931395939/5000000000 : ℝ)*X 2 1+(3048156241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2696455661/10000000000 : ℝ)*X 0 0+(811808997/2500000000 : ℝ)*X 0 1+(-422375631/625000000 : ℝ)*X 0 2+(2696455661/10000000000 : ℝ)*X 1 0+(811808997/2500000000 : ℝ)*X 1 1+(-422375631/625000000 : ℝ)*X 1 2+(2696455661/10000000000 : ℝ)*X 2 0+(811808997/2500000000 : ℝ)*X 2 1+(-422375631/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-441620449/10000000000 : ℝ)*X 0 0+(5772375899/10000000000 : ℝ)*X 0 1+(-2955511171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((603940259/625000000 : ℝ)*X 1 0+(-83841981/2500000000 : ℝ)*X 1 1+(-23535309/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1310523953/5000000000 : ℝ)*X 2 0+(1557632031/2500000000 : ℝ)*X 2 1+(988241223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4525679289/10000000000 : ℝ)*X 0 0+(1060762869/2000000000 : ℝ)*X 0 1+(-3130438103/10000000000 : ℝ)*X 0 2+(4525679289/10000000000 : ℝ)*X 1 0+(1060762869/2000000000 : ℝ)*X 1 1+(-3130438103/10000000000 : ℝ)*X 1 2+(4525679289/10000000000 : ℝ)*X 2 0+(1060762869/2000000000 : ℝ)*X 2 1+(-3130438103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((22409/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22409/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13295327657494015251807/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348487491599/500000000000 : ℝ)*(base39) + (113673828403/125000000000 : ℝ)*(base49) + (545983/250000000000 : ℝ)*(base53) + (581438791873/1000000000000 : ℝ)*(base60) + (2568664514647/1000000000000 : ℝ)*(major_s0_0) + (2568664514647/1000000000000 : ℝ)*(major_s0_1) + (513732466143/200000000000 : ℝ)*(major_s0_2) + (4638353/500000000000 : ℝ)*(sp_s0_1) + (51953/500000000000 : ℝ)*(sp_s0_6) + (1714828097103/500000000000 : ℝ)*(sp_s0_7) + (3429655124893/1000000000000 : ℝ)*(sp_s0_8) + (342966658553/100000000000 : ℝ)*(sp_s0_9) + (853830726749/500000000000 : ℝ)*(sp_s0_13) + (256481/31250000000 : ℝ)*(sp_s0_14) + (426915389351/250000000000 : ℝ)*(f.failure) + (342966658553/100000000000 : ℝ)*(f.sum) + (3747536288334469/10000000000000000000000000000 : ℝ)*base62 + (196115699659567/250000000000000000000000000 : ℝ)*base65 + (810342399384067/2000000000000000000000000000 : ℝ)*base66 + (246371394993877/400000000000000000000000000 : ℝ)*base68 + (793553579660603/2000000000000000000000000000 : ℝ)*base71 + (99722809689057/1250000000000000000000000000 : ℝ)*base72 + (659863562064057/1250000000000000000000000000 : ℝ)*base75 + (802560052984067/2000000000000000000000000000 : ℝ)*base77 + (1399917039432791/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (121/1250000000000000 : ℝ)*base87 + (121/1250000000000000 : ℝ)*base89 + (121/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((29057/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(29057/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (93276840018674513061/20000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529530159601/500000000000 : ℝ)*(base39) + (990087/500000000000 : ℝ)*(base40) + (32178978319/62500000000 : ℝ)*(base49) + (761687267907/1000000000000 : ℝ)*(base60) + (25019038921/8000000000 : ℝ)*(major_s0_0) + (25019038921/8000000000 : ℝ)*(major_s0_1) + (25019038921/8000000000 : ℝ)*(major_s0_2) + (8590251/1000000000000 : ℝ)*(sp_s0_1) + (16293001/1000000000000 : ℝ)*(sp_s0_7) + (1043910862041/250000000000 : ℝ)*(sp_s0_14) + (4175609380593/1000000000000 : ℝ)*(sp_s0_15) + (1043914935291/250000000000 : ℝ)*(sp_s0_16) + (2079098434467/1000000000000 : ℝ)*(sp_s0_20) + (522129/12500000000 : ℝ)*(sp_s0_22) + (2079098434467/1000000000000 : ℝ)*(f.failure) + (1043914935291/250000000000 : ℝ)*(f.sum) + (18416867098313/80000000000000000000000000 : ℝ)*base63 + (2863502966551/10000000000000000000000000 : ℝ)*base64 + (6792958296419/16000000000000000000000000 : ℝ)*base67 + (12678277020381/16000000000000000000000000 : ℝ)*base69 + (3779903913497/80000000000000000000000000 : ℝ)*base71 + (6343112257551/10000000000000000000000000 : ℝ)*base72 + (2752735979551/10000000000000000000000000 : ℝ)*base75 + (12008536129181/16000000000000000000000000 : ℝ)*base77 + (23792662778313/80000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1307/5000000000000000 : ℝ)*base87 + (1307/5000000000000000 : ℝ)*base89 + (1307/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-46031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-46031/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3709448621573249697189/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5485279/1000000000000 : ℝ)*(base11) + (936736058681/1000000000000 : ℝ)*(base39) + (277739195099/500000000000 : ℝ)*(base49) + (121661/50000000000 : ℝ)*(base50) + (153723045143/62500000000 : ℝ)*(major_s0_0) + (153723045143/62500000000 : ℝ)*(major_s0_1) + (153723045143/62500000000 : ℝ)*(major_s0_2) + (26696621/200000000000 : ℝ)*(sp_s0_2) + (843123/31250000000 : ℝ)*(sp_s0_9) + (1558547/1000000000000 : ℝ)*(sp_s0_15) + (820998474129/250000000000 : ℝ)*(sp_s0_21) + (205249863953/62500000000 : ℝ)*(sp_s0_22) + (1641919459377/500000000000 : ℝ)*(sp_s0_23) + (408783526507/250000000000 : ℝ)*(sp_s0_27) + (408783526507/250000000000 : ℝ)*(f.failure) + (656799876359/200000000000 : ℝ)*(f.sum) + (332461339558921/625000000000000000000000000 : ℝ)*base62 + (52674752323067/78125000000000000000000000 : ℝ)*base65 + (84098493255123/125000000000000000000000000 : ℝ)*base66 + (110129135467623/125000000000000000000000000 : ℝ)*base69 + (134965149297651/625000000000000000000000000 : ℝ)*base71 + (2588205614433/78125000000000000000000000 : ℝ)*base72 + (418982791817/78125000000000000000000000 : ℝ)*base74 + (88137400430123/125000000000000000000000000 : ℝ)*base77 + (420077339746421/625000000000000000000000000 : ℝ)*base79 + (853/1250000000000000 : ℝ)*base86 + (853/1250000000000000 : ℝ)*base88 + (853/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (22409/50000 : ℝ) ^ (131/32 : ℝ) ≤ (1871128280021961211/50000000000000000000 : ℝ) := by
    have hpowers : (22409/50000 : ℝ)^131 ≤ (1871128280021961211/50000000000000000000 : ℝ)^32 := by
      have hnat : (22409 : ℕ)^131*50000000000000000000^32 ≤ 1871128280021961211^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22409 50000 1871128280021961211 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22409/50000 : ℝ)) (X := (1871128280021961211/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51871128280021961211/50000000000000000000 : ℝ) ≤ (5045074427509399/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (51871128280021961211/50000000000000000000 : ℝ)^32 ≤ (5045074427509399/5000000000000000 : ℝ)^131 := by
      have hnat : (51871128280021961211 : ℕ)^32*5000000000000000^131 ≤ 5045074427509399^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51871128280021961211 50000000000000000000 5045074427509399 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045074427509399/5000000000000000 : ℝ)) (X := (51871128280021961211/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26871128280021961211/25000000000000000000 : ℝ) ≤ (10177872642384323/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (26871128280021961211/25000000000000000000 : ℝ)^32 ≤ (10177872642384323/10000000000000000 : ℝ)^131 := by
      have hnat : (26871128280021961211 : ℕ)^32*10000000000000000^131 ≤ 10177872642384323^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26871128280021961211 25000000000000000000 10177872642384323 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177872642384323/10000000000000000 : ℝ)) (X := (26871128280021961211/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(45074427509399/2240900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3508951494621/179272000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (22409/50000 : ℝ)) (alpha := (45074427509399/2240900000000000 : ℝ)) (beta := (3508951494621/179272000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22409/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(45074427509399/2240900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3508951494621/179272000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (29057/50000 : ℝ) ^ (131/32 : ℝ) ≤ (2167975619804870721/20000000000000000000 : ℝ) := by
    have hpowers : (29057/50000 : ℝ)^131 ≤ (2167975619804870721/20000000000000000000 : ℝ)^32 := by
      have hnat : (29057 : ℕ)^131*20000000000000000000^32 ≤ 2167975619804870721^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29057 50000 2167975619804870721 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29057/50000 : ℝ)) (X := (2167975619804870721/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (22167975619804870721/20000000000000000000 : ℝ) ≤ (5127292821378457/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (22167975619804870721/20000000000000000000 : ℝ)^32 ≤ (5127292821378457/5000000000000000 : ℝ)^131 := by
      have hnat : (22167975619804870721 : ℕ)^32*5000000000000000^131 ≤ 5127292821378457^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22167975619804870721 20000000000000000000 5127292821378457 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5127292821378457/5000000000000000 : ℝ)) (X := (22167975619804870721/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12167975619804870721/10000000000000000000 : ℝ) ≤ (5245497638507619/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (12167975619804870721/10000000000000000000 : ℝ)^32 ≤ (5245497638507619/5000000000000000 : ℝ)^131 := by
      have hnat : (12167975619804870721 : ℕ)^32*5000000000000000^131 ≤ 5245497638507619^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12167975619804870721 10000000000000000000 5245497638507619 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5245497638507619/5000000000000000 : ℝ)) (X := (12167975619804870721/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2597812681193/59300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(59102408564581/1452850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (29057/50000 : ℝ)) (alpha := (2597812681193/59300000000000 : ℝ)) (beta := (59102408564581/1452850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (29057/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2597812681193/59300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(59102408564581/1452850000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (46031/100000 : ℝ) ^ (131/32 : ℝ) ≤ (834915667594503237/20000000000000000000 : ℝ) := by
    have hpowers : (46031/100000 : ℝ)^131 ≤ (834915667594503237/20000000000000000000 : ℝ)^32 := by
      have hnat : (46031 : ℕ)^131*20000000000000000000^32 ≤ 834915667594503237^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46031 100000 834915667594503237 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46031/100000 : ℝ)) (X := (834915667594503237/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20834915667594503237/20000000000000000000 : ℝ) ≤ (10100404074080741/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (20834915667594503237/20000000000000000000 : ℝ)^32 ≤ (10100404074080741/10000000000000000 : ℝ)^131 := by
      have hnat : (20834915667594503237 : ℕ)^32*10000000000000000^131 ≤ 10100404074080741^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20834915667594503237 20000000000000000000 10100404074080741 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10100404074080741/10000000000000000 : ℝ)) (X := (20834915667594503237/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10834915667594503237/10000000000000000000 : ℝ) ≤ (10197811992145819/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10834915667594503237/10000000000000000000 : ℝ)^32 ≤ (10197811992145819/10000000000000000 : ℝ)^131 := by
      have hnat : (10834915667594503237 : ℕ)^32*10000000000000000^131 ≤ 10197811992145819^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10834915667594503237 10000000000000000000 10197811992145819 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10197811992145819/10000000000000000 : ℝ)) (X := (10834915667594503237/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(100404074080741/4603100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(48703959032539/2301550000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (46031/100000 : ℝ)) (alpha := (100404074080741/4603100000000000 : ℝ)) (beta := (48703959032539/2301550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (46031/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(100404074080741/4603100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(48703959032539/2301550000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-670372601/2500000000 : ℝ)*X 0 0+(4483151589/10000000000 : ℝ)*X 0 1+(-2854768009/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3262611703/5000000000 : ℝ)*X 1 0+(-90456989/312500000 : ℝ)*X 1 1+(-670102233/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((245162319/625000000 : ℝ)*X 2 0+(5236173207/10000000000 : ℝ)*X 2 1+(3848870147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((481756249/1250000000 : ℝ)*X 0 0+(2441824863/5000000000 : ℝ)*X 0 1+(-536794497/1250000000 : ℝ)*X 0 2+(481756249/1250000000 : ℝ)*X 1 0+(2441824863/5000000000 : ℝ)*X 1 1+(-536794497/1250000000 : ℝ)*X 1 2+(481756249/1250000000 : ℝ)*X 2 0+(2441824863/5000000000 : ℝ)*X 2 1+(-536794497/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-40081869613809754667329978330023/6687613835000000000000000000000 : ℝ) := by norm_num
    linear_combination (4609/1000000000000 : ℝ)*(base12) + (2211/125000000000 : ℝ)*(base15) + (167/20000000000 : ℝ)*(base25) + (6499/1000000000000 : ℝ)*(base33) + (375951649653/1000000000000 : ℝ)*(base39) + (273940856099/1000000000000 : ℝ)*(base49) + (38003670991/250000000000 : ℝ)*(base60) + (1504199993501/1000000000000 : ℝ)*(major_s1_0) + (7521/5000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (199781618707/100000000000 : ℝ)*(sp_s1_0) + (499454041873/250000000000 : ℝ)*(sp_s1_1) + (199781617683/100000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1997816191679/1000000000000 : ℝ)*(f.sum) + (16802735368118531669/334380691750000000000000000000 : ℝ)*base63 + (11560447896113/46031000000000000000000000 : ℝ)*base64 + (14793183192741/296500000000000000000000 : ℝ)*base66 + (10983781605289/57538750000000000000000000 : ℝ)*base68 + (13466782012229432491/103150867900000000000000000000000 : ℝ)*base70 + (48856903390617/179272000000000000000000000 : ℝ)*base73 + (90551346165011/1816062500000000000000000 : ℝ)*base75 + (206590185532999/2240900000000000000000000000 : ℝ)*base77 + (5314443729352624943/106308296000000000000000000000 : ℝ)*base78 + hcertificate_margin
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
theorem coarse_distinct_p003_b035 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c303079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10080 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b035 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
