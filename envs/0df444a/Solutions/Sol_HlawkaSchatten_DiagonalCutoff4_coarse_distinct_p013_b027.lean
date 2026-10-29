-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:12.060975+00:00
-- url     : https://prove2.me/submissions/3d78d4aa-3177-432d-9aaf-65611ecf7d55

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
theorem collision_support_c313068_s0_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3795924139/5000000000 : ℝ)*x 0 + (2780614459/10000000000 : ℝ)*x 1 + (-1658496561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3795924139/5000000000 : ℝ)^37 ≤ (70362285797547/100000000000000 : ℝ)^29 := by
    have hnat : (3795924139 : ℕ)^37*100000000000000^29 ≤ 70362285797547^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3795924139 5000000000 70362285797547 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2780614459/10000000000 : ℝ)^37 ≤ (19534410118559/100000000000000 : ℝ)^29 := by
    have hnat : (2780614459 : ℕ)^37*100000000000000^29 ≤ 19534410118559^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780614459 10000000000 19534410118559 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1658496561/10000000000 : ℝ)^37 ≤ (5051652034169/50000000000000 : ℝ)^29 := by
    have hnat : (1658496561 : ℕ)^37*50000000000000^29 ≤ 5051652034169^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658496561 10000000000 5051652034169 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3795924139/5000000000 : ℝ), (2780614459/10000000000 : ℝ), (-1658496561/10000000000 : ℝ)] ![(70362285797547/100000000000000 : ℝ), (19534410118559/100000000000000 : ℝ), (5051652034169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3795924139/5000000000 : ℝ)|^37 ≤ (70362285797547/100000000000000 : ℝ)^29
        have hw : |(3795924139/5000000000 : ℝ)|=(3795924139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2780614459/10000000000 : ℝ)|^37 ≤ (19534410118559/100000000000000 : ℝ)^29
        have hw : |(2780614459/10000000000 : ℝ)|=(2780614459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1658496561/10000000000 : ℝ)|^37 ≤ (5051652034169/50000000000000 : ℝ)^29
        have hw : |(-1658496561/10000000000 : ℝ)|=(1658496561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4139445019/10000000000 : ℝ)*x 0 + (-2176326703/5000000000 : ℝ)*x 1 + (1047079723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4139445019/10000000000 : ℝ)^37 ≤ (16227102641051/50000000000000 : ℝ)^29 := by
    have hnat : (4139445019 : ℕ)^37*50000000000000^29 ≤ 16227102641051^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139445019 10000000000 16227102641051 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176326703/5000000000 : ℝ)^37 ≤ (34601907540613/100000000000000 : ℝ)^29 := by
    have hnat : (2176326703 : ℕ)^37*100000000000000^29 ≤ 34601907540613^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176326703 5000000000 34601907540613 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047079723/2500000000 : ℝ)^37 ≤ (32943887155459/100000000000000 : ℝ)^29 := by
    have hnat : (1047079723 : ℕ)^37*100000000000000^29 ≤ 32943887155459^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047079723 2500000000 32943887155459 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4139445019/10000000000 : ℝ), (-2176326703/5000000000 : ℝ), (1047079723/2500000000 : ℝ)] ![(16227102641051/50000000000000 : ℝ), (34601907540613/100000000000000 : ℝ), (32943887155459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4139445019/10000000000 : ℝ)|^37 ≤ (16227102641051/50000000000000 : ℝ)^29
        have hw : |(4139445019/10000000000 : ℝ)|=(4139445019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176326703/5000000000 : ℝ)|^37 ≤ (34601907540613/100000000000000 : ℝ)^29
        have hw : |(-2176326703/5000000000 : ℝ)|=(2176326703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047079723/2500000000 : ℝ)|^37 ≤ (32943887155459/100000000000000 : ℝ)^29
        have hw : |(1047079723/2500000000 : ℝ)|=(1047079723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-110210851/2000000000 : ℝ)*x 0 + (-5569565903/10000000000 : ℝ)*x 1 + (-2910175799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110210851/2000000000 : ℝ)^37 ≤ (49541326123/2000000000000 : ℝ)^29 := by
    have hnat : (110210851 : ℕ)^37*2000000000000^29 ≤ 49541326123^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110210851 2000000000 49541326123 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569565903/10000000000 : ℝ)^37 ≤ (23695894220547/50000000000000 : ℝ)^29 := by
    have hnat : (5569565903 : ℕ)^37*50000000000000^29 ≤ 23695894220547^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569565903 10000000000 23695894220547 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2910175799/5000000000 : ℝ)^37 ≤ (25065572618967/50000000000000 : ℝ)^29 := by
    have hnat : (2910175799 : ℕ)^37*50000000000000^29 ≤ 25065572618967^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2910175799 5000000000 25065572618967 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110210851/2000000000 : ℝ), (-5569565903/10000000000 : ℝ), (-2910175799/5000000000 : ℝ)] ![(49541326123/2000000000000 : ℝ), (23695894220547/50000000000000 : ℝ), (25065572618967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110210851/2000000000 : ℝ)|^37 ≤ (49541326123/2000000000000 : ℝ)^29
        have hw : |(-110210851/2000000000 : ℝ)|=(110210851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5569565903/10000000000 : ℝ)|^37 ≤ (23695894220547/50000000000000 : ℝ)^29
        have hw : |(-5569565903/10000000000 : ℝ)|=(5569565903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2910175799/5000000000 : ℝ)|^37 ≤ (25065572618967/50000000000000 : ℝ)^29
        have hw : |(-2910175799/5000000000 : ℝ)|=(2910175799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3818093927/5000000000 : ℝ)*x 0 + (824058703/2500000000 : ℝ)*x 1 + (-932095807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3818093927/5000000000 : ℝ)^37 ≤ (70887017019359/100000000000000 : ℝ)^29 := by
    have hnat : (3818093927 : ℕ)^37*100000000000000^29 ≤ 70887017019359^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3818093927 5000000000 70887017019359 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824058703/2500000000 : ℝ)^37 ≤ (6067330293979/25000000000000 : ℝ)^29 := by
    have hnat : (824058703 : ℕ)^37*25000000000000^29 ≤ 6067330293979^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824058703 2500000000 6067330293979 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932095807/10000000000 : ℝ)^37 ≤ (4843661788723/100000000000000 : ℝ)^29 := by
    have hnat : (932095807 : ℕ)^37*100000000000000^29 ≤ 4843661788723^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932095807 10000000000 4843661788723 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3818093927/5000000000 : ℝ), (824058703/2500000000 : ℝ), (-932095807/10000000000 : ℝ)] ![(70887017019359/100000000000000 : ℝ), (6067330293979/25000000000000 : ℝ), (4843661788723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3818093927/5000000000 : ℝ)|^37 ≤ (70887017019359/100000000000000 : ℝ)^29
        have hw : |(3818093927/5000000000 : ℝ)|=(3818093927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824058703/2500000000 : ℝ)|^37 ≤ (6067330293979/25000000000000 : ℝ)^29
        have hw : |(824058703/2500000000 : ℝ)|=(824058703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-932095807/10000000000 : ℝ)|^37 ≤ (4843661788723/100000000000000 : ℝ)^29
        have hw : |(-932095807/10000000000 : ℝ)|=(932095807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2291406183/5000000000 : ℝ)*x 0 + (-605751771/2000000000 : ℝ)*x 1 + (1249137497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2291406183/5000000000 : ℝ)^37 ≤ (36953133395573/100000000000000 : ℝ)^29 := by
    have hnat : (2291406183 : ℕ)^37*100000000000000^29 ≤ 36953133395573^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291406183 5000000000 36953133395573 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605751771/2000000000 : ℝ)^37 ≤ (10892694093569/50000000000000 : ℝ)^29 := by
    have hnat : (605751771 : ℕ)^37*50000000000000^29 ≤ 10892694093569^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605751771 2000000000 10892694093569 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249137497/2500000000 : ℝ)^37 ≤ (10315369600371/25000000000000 : ℝ)^29 := by
    have hnat : (1249137497 : ℕ)^37*25000000000000^29 ≤ 10315369600371^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249137497 2500000000 10315369600371 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2291406183/5000000000 : ℝ), (-605751771/2000000000 : ℝ), (1249137497/2500000000 : ℝ)] ![(36953133395573/100000000000000 : ℝ), (10892694093569/50000000000000 : ℝ), (10315369600371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2291406183/5000000000 : ℝ)|^37 ≤ (36953133395573/100000000000000 : ℝ)^29
        have hw : |(2291406183/5000000000 : ℝ)|=(2291406183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605751771/2000000000 : ℝ)|^37 ≤ (10892694093569/50000000000000 : ℝ)^29
        have hw : |(-605751771/2000000000 : ℝ)|=(605751771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249137497/2500000000 : ℝ)|^37 ≤ (10315369600371/25000000000000 : ℝ)^29
        have hw : |(1249137497/2500000000 : ℝ)|=(1249137497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (984415777/2000000000 : ℝ)*x 0 + (-783025807/5000000000 : ℝ)*x 1 + (-2910175799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984415777/2000000000 : ℝ)^37 ≤ (40478465203893/100000000000000 : ℝ)^29 := by
    have hnat : (984415777 : ℕ)^37*100000000000000^29 ≤ 40478465203893^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984415777 2000000000 40478465203893 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (783025807/5000000000 : ℝ)^37 ≤ (9390389540023/100000000000000 : ℝ)^29 := by
    have hnat : (783025807 : ℕ)^37*100000000000000^29 ≤ 9390389540023^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783025807 5000000000 9390389540023 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2910175799/5000000000 : ℝ)^37 ≤ (25065572618967/50000000000000 : ℝ)^29 := by
    have hnat : (2910175799 : ℕ)^37*50000000000000^29 ≤ 25065572618967^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2910175799 5000000000 25065572618967 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984415777/2000000000 : ℝ), (-783025807/5000000000 : ℝ), (-2910175799/5000000000 : ℝ)] ![(40478465203893/100000000000000 : ℝ), (9390389540023/100000000000000 : ℝ), (25065572618967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984415777/2000000000 : ℝ)|^37 ≤ (40478465203893/100000000000000 : ℝ)^29
        have hw : |(984415777/2000000000 : ℝ)|=(984415777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-783025807/5000000000 : ℝ)|^37 ≤ (9390389540023/100000000000000 : ℝ)^29
        have hw : |(-783025807/5000000000 : ℝ)|=(783025807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2910175799/5000000000 : ℝ)|^37 ≤ (25065572618967/50000000000000 : ℝ)^29
        have hw : |(-2910175799/5000000000 : ℝ)|=(2910175799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-24836117/1250000000 : ℝ)*x 0 + (-430079701/1000000000 : ℝ)*x 1 + (-7155938551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24836117/1250000000 : ℝ)^37 ≤ (337034500681/50000000000000 : ℝ)^29 := by
    have hnat : (24836117 : ℕ)^37*50000000000000^29 ≤ 337034500681^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24836117 1250000000 337034500681 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430079701/1000000000 : ℝ)^37 ≤ (34076815188811/100000000000000 : ℝ)^29 := by
    have hnat : (430079701 : ℕ)^37*100000000000000^29 ≤ 34076815188811^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430079701 1000000000 34076815188811 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7155938551/10000000000 : ℝ)^37 ≤ (32624557899749/50000000000000 : ℝ)^29 := by
    have hnat : (7155938551 : ℕ)^37*50000000000000^29 ≤ 32624557899749^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7155938551 10000000000 32624557899749 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24836117/1250000000 : ℝ), (-430079701/1000000000 : ℝ), (-7155938551/10000000000 : ℝ)] ![(337034500681/50000000000000 : ℝ), (34076815188811/100000000000000 : ℝ), (32624557899749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24836117/1250000000 : ℝ)|^37 ≤ (337034500681/50000000000000 : ℝ)^29
        have hw : |(-24836117/1250000000 : ℝ)|=(24836117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430079701/1000000000 : ℝ)|^37 ≤ (34076815188811/100000000000000 : ℝ)^29
        have hw : |(-430079701/1000000000 : ℝ)|=(430079701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7155938551/10000000000 : ℝ)|^37 ≤ (32624557899749/50000000000000 : ℝ)^29
        have hw : |(-7155938551/10000000000 : ℝ)|=(7155938551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (355446707/400000000 : ℝ)*x 0 + (463995901/2500000000 : ℝ)*x 1 + (-524130043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355446707/400000000 : ℝ)^37 ≤ (344054127273/400000000000 : ℝ)^29 := by
    have hnat : (355446707 : ℕ)^37*400000000000^29 ≤ 344054127273^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355446707 400000000 344054127273 400000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463995901/2500000000 : ℝ)^37 ≤ (11662763874671/100000000000000 : ℝ)^29 := by
    have hnat : (463995901 : ℕ)^37*100000000000000^29 ≤ 11662763874671^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463995901 2500000000 11662763874671 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524130043/10000000000 : ℝ)^37 ≤ (29046303779/1250000000000 : ℝ)^29 := by
    have hnat : (524130043 : ℕ)^37*1250000000000^29 ≤ 29046303779^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524130043 10000000000 29046303779 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(355446707/400000000 : ℝ), (463995901/2500000000 : ℝ), (-524130043/10000000000 : ℝ)] ![(344054127273/400000000000 : ℝ), (11662763874671/100000000000000 : ℝ), (29046303779/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(355446707/400000000 : ℝ)|^37 ≤ (344054127273/400000000000 : ℝ)^29
        have hw : |(355446707/400000000 : ℝ)|=(355446707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463995901/2500000000 : ℝ)|^37 ≤ (11662763874671/100000000000000 : ℝ)^29
        have hw : |(463995901/2500000000 : ℝ)|=(463995901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524130043/10000000000 : ℝ)|^37 ≤ (29046303779/1250000000000 : ℝ)^29
        have hw : |(-524130043/10000000000 : ℝ)|=(524130043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (578964381/1250000000 : ℝ)*x 0 + (-1128520379/2500000000 : ℝ)*x 1 + (1755022437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578964381/1250000000 : ℝ)^37 ≤ (18728486734247/50000000000000 : ℝ)^29 := by
    have hnat : (578964381 : ℕ)^37*50000000000000^29 ≤ 18728486734247^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578964381 1250000000 18728486734247 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128520379/2500000000 : ℝ)^37 ≤ (9061877881881/25000000000000 : ℝ)^29 := by
    have hnat : (1128520379 : ℕ)^37*25000000000000^29 ≤ 9061877881881^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128520379 2500000000 9061877881881 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1755022437/5000000000 : ℝ)^37 ≤ (1643469686931/6250000000000 : ℝ)^29 := by
    have hnat : (1755022437 : ℕ)^37*6250000000000^29 ≤ 1643469686931^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755022437 5000000000 1643469686931 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578964381/1250000000 : ℝ), (-1128520379/2500000000 : ℝ), (1755022437/5000000000 : ℝ)] ![(18728486734247/50000000000000 : ℝ), (9061877881881/25000000000000 : ℝ), (1643469686931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578964381/1250000000 : ℝ)|^37 ≤ (18728486734247/50000000000000 : ℝ)^29
        have hw : |(578964381/1250000000 : ℝ)|=(578964381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128520379/2500000000 : ℝ)|^37 ≤ (9061877881881/25000000000000 : ℝ)^29
        have hw : |(-1128520379/2500000000 : ℝ)|=(1128520379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1755022437/5000000000 : ℝ)|^37 ≤ (1643469686931/6250000000000 : ℝ)^29
        have hw : |(1755022437/5000000000 : ℝ)|=(1755022437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1276409343/5000000000 : ℝ)*x 0 + (-2520610893/10000000000 : ℝ)*x 1 + (-7155938551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1276409343/5000000000 : ℝ)^37 ≤ (8758087434507/50000000000000 : ℝ)^29 := by
    have hnat : (1276409343 : ℕ)^37*50000000000000^29 ≤ 8758087434507^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276409343 5000000000 8758087434507 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2520610893/10000000000 : ℝ)^37 ≤ (8617354657833/50000000000000 : ℝ)^29 := by
    have hnat : (2520610893 : ℕ)^37*50000000000000^29 ≤ 8617354657833^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520610893 10000000000 8617354657833 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7155938551/10000000000 : ℝ)^37 ≤ (32624557899749/50000000000000 : ℝ)^29 := by
    have hnat : (7155938551 : ℕ)^37*50000000000000^29 ≤ 32624557899749^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7155938551 10000000000 32624557899749 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1276409343/5000000000 : ℝ), (-2520610893/10000000000 : ℝ), (-7155938551/10000000000 : ℝ)] ![(8758087434507/50000000000000 : ℝ), (8617354657833/50000000000000 : ℝ), (32624557899749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1276409343/5000000000 : ℝ)|^37 ≤ (8758087434507/50000000000000 : ℝ)^29
        have hw : |(1276409343/5000000000 : ℝ)|=(1276409343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2520610893/10000000000 : ℝ)|^37 ≤ (8617354657833/50000000000000 : ℝ)^29
        have hw : |(-2520610893/10000000000 : ℝ)|=(2520610893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7155938551/10000000000 : ℝ)|^37 ≤ (32624557899749/50000000000000 : ℝ)^29
        have hw : |(-7155938551/10000000000 : ℝ)|=(7155938551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-174282971/10000000000 : ℝ)*x 0 + (-6333144129/10000000000 : ℝ)*x 1 + (-652104319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174282971/10000000000 : ℝ)^37 ≤ (570274441389/100000000000000 : ℝ)^29 := by
    have hnat : (174282971 : ℕ)^37*100000000000000^29 ≤ 570274441389^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174282971 10000000000 570274441389 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6333144129/10000000000 : ℝ)^37 ≤ (55833349347601/100000000000000 : ℝ)^29 := by
    have hnat : (6333144129 : ℕ)^37*100000000000000^29 ≤ 55833349347601^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6333144129 10000000000 55833349347601 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652104319/1250000000 : ℝ)^37 ≤ (43596376198877/100000000000000 : ℝ)^29 := by
    have hnat : (652104319 : ℕ)^37*100000000000000^29 ≤ 43596376198877^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652104319 1250000000 43596376198877 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174282971/10000000000 : ℝ), (-6333144129/10000000000 : ℝ), (-652104319/1250000000 : ℝ)] ![(570274441389/100000000000000 : ℝ), (55833349347601/100000000000000 : ℝ), (43596376198877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174282971/10000000000 : ℝ)|^37 ≤ (570274441389/100000000000000 : ℝ)^29
        have hw : |(-174282971/10000000000 : ℝ)|=(174282971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6333144129/10000000000 : ℝ)|^37 ≤ (55833349347601/100000000000000 : ℝ)^29
        have hw : |(-6333144129/10000000000 : ℝ)|=(6333144129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652104319/1250000000 : ℝ)|^37 ≤ (43596376198877/100000000000000 : ℝ)^29
        have hw : |(-652104319/1250000000 : ℝ)|=(652104319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8982413041/10000000000 : ℝ)*x 0 + (214202553/1250000000 : ℝ)*x 1 + (-128315309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8982413041/10000000000 : ℝ)^37 ≤ (87203903159991/100000000000000 : ℝ)^29 := by
    have hnat : (8982413041 : ℕ)^37*100000000000000^29 ≤ 87203903159991^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8982413041 10000000000 87203903159991 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214202553/1250000000 : ℝ)^37 ≤ (1053369488173/10000000000000 : ℝ)^29 := by
    have hnat : (214202553 : ℕ)^37*10000000000000^29 ≤ 1053369488173^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214202553 1250000000 1053369488173 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128315309/2500000000 : ℝ)^37 ≤ (141400121819/6250000000000 : ℝ)^29 := by
    have hnat : (128315309 : ℕ)^37*6250000000000^29 ≤ 141400121819^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128315309 2500000000 141400121819 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8982413041/10000000000 : ℝ), (214202553/1250000000 : ℝ), (-128315309/2500000000 : ℝ)] ![(87203903159991/100000000000000 : ℝ), (1053369488173/10000000000000 : ℝ), (141400121819/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8982413041/10000000000 : ℝ)|^37 ≤ (87203903159991/100000000000000 : ℝ)^29
        have hw : |(8982413041/10000000000 : ℝ)|=(8982413041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214202553/1250000000 : ℝ)|^37 ≤ (1053369488173/10000000000000 : ℝ)^29
        have hw : |(214202553/1250000000 : ℝ)|=(214202553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128315309/2500000000 : ℝ)|^37 ≤ (141400121819/6250000000000 : ℝ)^29
        have hw : |(-128315309/2500000000 : ℝ)|=(128315309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3483404911/10000000000 : ℝ)*x 0 + (-4611372399/10000000000 : ℝ)*x 1 + (569915253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3483404911/10000000000 : ℝ)^37 ≤ (26041153922019/100000000000000 : ℝ)^29 := by
    have hnat : (3483404911 : ℕ)^37*100000000000000^29 ≤ 26041153922019^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3483404911 10000000000 26041153922019 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4611372399/10000000000 : ℝ)^37 ≤ (9311801440683/25000000000000 : ℝ)^29 := by
    have hnat : (4611372399 : ℕ)^37*25000000000000^29 ≤ 9311801440683^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611372399 10000000000 9311801440683 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569915253/1250000000 : ℝ)^37 ≤ (36711640297107/100000000000000 : ℝ)^29 := by
    have hnat : (569915253 : ℕ)^37*100000000000000^29 ≤ 36711640297107^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569915253 1250000000 36711640297107 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3483404911/10000000000 : ℝ), (-4611372399/10000000000 : ℝ), (569915253/1250000000 : ℝ)] ![(26041153922019/100000000000000 : ℝ), (9311801440683/25000000000000 : ℝ), (36711640297107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3483404911/10000000000 : ℝ)|^37 ≤ (26041153922019/100000000000000 : ℝ)^29
        have hw : |(3483404911/10000000000 : ℝ)|=(3483404911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4611372399/10000000000 : ℝ)|^37 ≤ (9311801440683/25000000000000 : ℝ)^29
        have hw : |(-4611372399/10000000000 : ℝ)|=(4611372399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569915253/1250000000 : ℝ)|^37 ≤ (36711640297107/100000000000000 : ℝ)^29
        have hw : |(569915253/1250000000 : ℝ)|=(569915253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s0_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (249508783/625000000 : ℝ)*x 0 + (-683529947/2000000000 : ℝ)*x 1 + (-652104319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249508783/625000000 : ℝ)^37 ≤ (7747001531029/25000000000000 : ℝ)^29 := by
    have hnat : (249508783 : ℕ)^37*25000000000000^29 ≤ 7747001531029^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249508783 625000000 7747001531029 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683529947/2000000000 : ℝ)^37 ≤ (3176952208003/12500000000000 : ℝ)^29 := by
    have hnat : (683529947 : ℕ)^37*12500000000000^29 ≤ 3176952208003^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683529947 2000000000 3176952208003 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652104319/1250000000 : ℝ)^37 ≤ (43596376198877/100000000000000 : ℝ)^29 := by
    have hnat : (652104319 : ℕ)^37*100000000000000^29 ≤ 43596376198877^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652104319 1250000000 43596376198877 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249508783/625000000 : ℝ), (-683529947/2000000000 : ℝ), (-652104319/1250000000 : ℝ)] ![(7747001531029/25000000000000 : ℝ), (3176952208003/12500000000000 : ℝ), (43596376198877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249508783/625000000 : ℝ)|^37 ≤ (7747001531029/25000000000000 : ℝ)^29
        have hw : |(249508783/625000000 : ℝ)|=(249508783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-683529947/2000000000 : ℝ)|^37 ≤ (3176952208003/12500000000000 : ℝ)^29
        have hw : |(-683529947/2000000000 : ℝ)|=(683529947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652104319/1250000000 : ℝ)|^37 ≤ (43596376198877/100000000000000 : ℝ)^29
        have hw : |(-652104319/1250000000 : ℝ)|=(652104319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-114405353/500000000 : ℝ)*x 0 + (-301496931/625000000 : ℝ)*x 1 + (-1075478343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114405353/500000000 : ℝ)^37 ≤ (7616407354373/50000000000000 : ℝ)^29 := by
    have hnat : (114405353 : ℕ)^37*50000000000000^29 ≤ 7616407354373^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114405353 500000000 7616407354373 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301496931/625000000 : ℝ)^37 ≤ (39451701761901/100000000000000 : ℝ)^29 := by
    have hnat : (301496931 : ℕ)^37*100000000000000^29 ≤ 39451701761901^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301496931 625000000 39451701761901 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075478343/2000000000 : ℝ)^37 ≤ (22657741754007/50000000000000 : ℝ)^29 := by
    have hnat : (1075478343 : ℕ)^37*50000000000000^29 ≤ 22657741754007^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075478343 2000000000 22657741754007 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114405353/500000000 : ℝ), (-301496931/625000000 : ℝ), (-1075478343/2000000000 : ℝ)] ![(7616407354373/50000000000000 : ℝ), (39451701761901/100000000000000 : ℝ), (22657741754007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114405353/500000000 : ℝ)|^37 ≤ (7616407354373/50000000000000 : ℝ)^29
        have hw : |(-114405353/500000000 : ℝ)|=(114405353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-301496931/625000000 : ℝ)|^37 ≤ (39451701761901/100000000000000 : ℝ)^29
        have hw : |(-301496931/625000000 : ℝ)|=(301496931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075478343/2000000000 : ℝ)|^37 ≤ (22657741754007/50000000000000 : ℝ)^29
        have hw : |(-1075478343/2000000000 : ℝ)|=(1075478343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s1_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6199945803/10000000000 : ℝ)*x 0 + (10316441/31250000 : ℝ)*x 1 + (-2980551303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6199945803/10000000000 : ℝ)^37 ≤ (54339493717877/100000000000000 : ℝ)^29 := by
    have hnat : (6199945803 : ℕ)^37*100000000000000^29 ≤ 54339493717877^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6199945803 10000000000 54339493717877 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10316441/31250000 : ℝ)^37 ≤ (24316547442179/100000000000000 : ℝ)^29 := by
    have hnat : (10316441 : ℕ)^37*100000000000000^29 ≤ 24316547442179^29*31250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10316441 31250000 24316547442179 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980551303/10000000000 : ℝ)^37 ≤ (10671979411859/50000000000000 : ℝ)^29 := by
    have hnat : (2980551303 : ℕ)^37*50000000000000^29 ≤ 10671979411859^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980551303 10000000000 10671979411859 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6199945803/10000000000 : ℝ), (10316441/31250000 : ℝ), (-2980551303/10000000000 : ℝ)] ![(54339493717877/100000000000000 : ℝ), (24316547442179/100000000000000 : ℝ), (10671979411859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6199945803/10000000000 : ℝ)|^37 ≤ (54339493717877/100000000000000 : ℝ)^29
        have hw : |(6199945803/10000000000 : ℝ)|=(6199945803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10316441/31250000 : ℝ)|^37 ≤ (24316547442179/100000000000000 : ℝ)^29
        have hw : |(10316441/31250000 : ℝ)|=(10316441/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2980551303/10000000000 : ℝ)|^37 ≤ (10671979411859/50000000000000 : ℝ)^29
        have hw : |(-2980551303/10000000000 : ℝ)|=(2980551303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2094051981/5000000000 : ℝ)*x 0 + (-4461721919/10000000000 : ℝ)*x 1 + (4028276041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094051981/5000000000 : ℝ)^37 ≤ (16470865120823/50000000000000 : ℝ)^29 := by
    have hnat : (2094051981 : ℕ)^37*50000000000000^29 ≤ 16470865120823^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094051981 5000000000 16470865120823 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4461721919/10000000000 : ℝ)^37 ≤ (17855973697169/50000000000000 : ℝ)^29 := by
    have hnat : (4461721919 : ℕ)^37*50000000000000^29 ≤ 17855973697169^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461721919 10000000000 17855973697169 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028276041/10000000000 : ℝ)^37 ≤ (31346322342083/100000000000000 : ℝ)^29 := by
    have hnat : (4028276041 : ℕ)^37*100000000000000^29 ≤ 31346322342083^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028276041 10000000000 31346322342083 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094051981/5000000000 : ℝ), (-4461721919/10000000000 : ℝ), (4028276041/10000000000 : ℝ)] ![(16470865120823/50000000000000 : ℝ), (17855973697169/50000000000000 : ℝ), (31346322342083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094051981/5000000000 : ℝ)|^37 ≤ (16470865120823/50000000000000 : ℝ)^29
        have hw : |(2094051981/5000000000 : ℝ)|=(2094051981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4461721919/10000000000 : ℝ)|^37 ≤ (17855973697169/50000000000000 : ℝ)^29
        have hw : |(-4461721919/10000000000 : ℝ)|=(4461721919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028276041/10000000000 : ℝ)|^37 ≤ (31346322342083/100000000000000 : ℝ)^29
        have hw : |(4028276041/10000000000 : ℝ)|=(4028276041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313068_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (981394477/2500000000 : ℝ)*x 0 + (-2068269279/5000000000 : ℝ)*x 1 + (-4611114137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981394477/2500000000 : ℝ)^37 ≤ (30330321095339/100000000000000 : ℝ)^29 := by
    have hnat : (981394477 : ℕ)^37*100000000000000^29 ≤ 30330321095339^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981394477 2500000000 30330321095339 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068269279/5000000000 : ℝ)^37 ≤ (32425134613711/100000000000000 : ℝ)^29 := by
    have hnat : (2068269279 : ℕ)^37*100000000000000^29 ≤ 32425134613711^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068269279 5000000000 32425134613711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4611114137/10000000000 : ℝ)^37 ≤ (18622272137761/50000000000000 : ℝ)^29 := by
    have hnat : (4611114137 : ℕ)^37*50000000000000^29 ≤ 18622272137761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611114137 10000000000 18622272137761 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(981394477/2500000000 : ℝ), (-2068269279/5000000000 : ℝ), (-4611114137/10000000000 : ℝ)] ![(30330321095339/100000000000000 : ℝ), (32425134613711/100000000000000 : ℝ), (18622272137761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(981394477/2500000000 : ℝ)|^37 ≤ (30330321095339/100000000000000 : ℝ)^29
        have hw : |(981394477/2500000000 : ℝ)|=(981394477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068269279/5000000000 : ℝ)|^37 ≤ (32425134613711/100000000000000 : ℝ)^29
        have hw : |(-2068269279/5000000000 : ℝ)|=(2068269279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4611114137/10000000000 : ℝ)|^37 ≤ (18622272137761/50000000000000 : ℝ)^29
        have hw : |(-4611114137/10000000000 : ℝ)|=(4611114137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313068 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3795924139/5000000000 : ℝ)*X 1 0+(2780614459/10000000000 : ℝ)*X 1 1+(-1658496561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4139445019/10000000000 : ℝ)*X 2 0+(-2176326703/5000000000 : ℝ)*X 2 1+(1047079723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-110210851/2000000000 : ℝ)*X 0 0+(-5569565903/10000000000 : ℝ)*X 0 1+(-2910175799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3818093927/5000000000 : ℝ)*X 1 0+(824058703/2500000000 : ℝ)*X 1 1+(-932095807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2291406183/5000000000 : ℝ)*X 2 0+(-605751771/2000000000 : ℝ)*X 2 1+(1249137497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((984415777/2000000000 : ℝ)*X 0 0+(-783025807/5000000000 : ℝ)*X 0 1+(-2910175799/5000000000 : ℝ)*X 0 2+(984415777/2000000000 : ℝ)*X 1 0+(-783025807/5000000000 : ℝ)*X 1 1+(-2910175799/5000000000 : ℝ)*X 1 2+(984415777/2000000000 : ℝ)*X 2 0+(-783025807/5000000000 : ℝ)*X 2 1+(-2910175799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-24836117/1250000000 : ℝ)*X 0 0+(-430079701/1000000000 : ℝ)*X 0 1+(-7155938551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((355446707/400000000 : ℝ)*X 1 0+(463995901/2500000000 : ℝ)*X 1 1+(-524130043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((578964381/1250000000 : ℝ)*X 2 0+(-1128520379/2500000000 : ℝ)*X 2 1+(1755022437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1276409343/5000000000 : ℝ)*X 0 0+(-2520610893/10000000000 : ℝ)*X 0 1+(-7155938551/10000000000 : ℝ)*X 0 2+(1276409343/5000000000 : ℝ)*X 1 0+(-2520610893/10000000000 : ℝ)*X 1 1+(-7155938551/10000000000 : ℝ)*X 1 2+(1276409343/5000000000 : ℝ)*X 2 0+(-2520610893/10000000000 : ℝ)*X 2 1+(-7155938551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-174282971/10000000000 : ℝ)*X 0 0+(-6333144129/10000000000 : ℝ)*X 0 1+(-652104319/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8982413041/10000000000 : ℝ)*X 1 0+(214202553/1250000000 : ℝ)*X 1 1+(-128315309/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3483404911/10000000000 : ℝ)*X 2 0+(-4611372399/10000000000 : ℝ)*X 2 1+(569915253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((249508783/625000000 : ℝ)*X 0 0+(-683529947/2000000000 : ℝ)*X 0 1+(-652104319/1250000000 : ℝ)*X 0 2+(249508783/625000000 : ℝ)*X 1 0+(-683529947/2000000000 : ℝ)*X 1 1+(-652104319/1250000000 : ℝ)*X 1 2+(249508783/625000000 : ℝ)*X 2 0+(-683529947/2000000000 : ℝ)*X 2 1+(-652104319/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((19757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (54342424495258563/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1415784333403/1000000000000 : ℝ)*(base1) + (184946749539/100000000000 : ℝ)*(base39) + (3892069259/10000000000 : ℝ)*(base49) + (245918966563/100000000000 : ℝ)*(major_s0_0) + (245918966563/100000000000 : ℝ)*(major_s0_1) + (245918966563/100000000000 : ℝ)*(major_s0_2) + (18395227/500000000000 : ℝ)*(sp_s0_1) + (15259985127/3125000000 : ℝ)*(sp_s0_7) + (1733686502359/500000000000 : ℝ)*(sp_s0_8) + (1733695359413/500000000000 : ℝ)*(sp_s0_9) + (2198519373/62500000000 : ℝ)*(sp_s0_13) + (5969231/1000000000000 : ℝ)*(sp_s0_14) + (7081297/1000000000000 : ℝ)*(sp_s0_15) + (26157643/1000000000000 : ℝ)*(sp_s0_23) + (1450960643371/1000000000000 : ℝ)*(f.failure) + (866854219117/250000000000 : ℝ)*(f.sum) + (51292668284059/200000000000000000000000000 : ℝ)*base63 + (361257814597341/1000000000000000000000000000 : ℝ)*base65 + (197459037538523/500000000000000000000000000 : ℝ)*base67 + (641755921238523/500000000000000000000000000 : ℝ)*base68 + (46767515195941/200000000000000000000000000 : ℝ)*base70 + (616768819102659/1000000000000000000000000000 : ℝ)*base73 + (481482020502659/1000000000000000000000000000 : ℝ)*base74 + (363035162661477/500000000000000000000000000 : ℝ)*base77 + (57815646684059/200000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (20677/100000000000000000 : ℝ)*base87 + (20677/100000000000000000 : ℝ)*base89 + (20677/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-26459/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-26459/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (920441938323729713409/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (42059737093/31250000000 : ℝ)*(base1) + (4707621/1000000000000 : ℝ)*(base21) + (2444502012463/1000000000000 : ℝ)*(base39) + (336756483373/500000000000 : ℝ)*(base49) + (138241657087/250000000000 : ℝ)*(base60) + (935919046271/250000000000 : ℝ)*(major_s0_0) + (935919046271/250000000000 : ℝ)*(major_s0_1) + (935919046271/250000000000 : ℝ)*(major_s0_2) + (15278263/1000000000000 : ℝ)*(sp_s0_8) + (21243967/1000000000000 : ℝ)*(sp_s0_9) + (6624434068623/1000000000000 : ℝ)*(sp_s0_14) + (1055701440677/200000000000 : ℝ)*(sp_s0_15) + (2639248265029/500000000000 : ℝ)*(sp_s0_16) + (862916337929/1000000000000 : ℝ)*(sp_s0_20) + (441765584981/200000000000 : ℝ)*(f.failure) + (5278522481647/1000000000000 : ℝ)*(f.sum) + (165563202986103/500000000000000000000000000 : ℝ)*base63 + (928990522467697/2500000000000000000000000000 : ℝ)*base65 + (119740023643591/1250000000000000000000000000 : ℝ)*base67 + (1326034101018591/1250000000000000000000000000 : ℝ)*base68 + (150809013663897/500000000000000000000000000 : ℝ)*base70 + (382836146967697/2500000000000000000000000000 : ℝ)*base72 + (1585283565717697/2500000000000000000000000000 : ℝ)*base75 + (43610965893591/1250000000000000000000000000 : ℝ)*base76 + (117614721736103/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (5253/20000000000000000 : ℝ)*base86 + (5253/20000000000000000 : ℝ)*base88 + (5253/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37793/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37793/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73265565910451581450359/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145751671997/1000000000000 : ℝ)*(base1) + (130008358593/100000000000 : ℝ)*(base39) + (575165105959/1000000000000 : ℝ)*(base49) + (15593689/1000000000000 : ℝ)*(base60) + (3131044779131/1000000000000 : ℝ)*(major_s0_0) + (3131044779131/1000000000000 : ℝ)*(major_s0_1) + (3131044779131/1000000000000 : ℝ)*(major_s0_2) + (19271527/200000000000 : ℝ)*(sp_s0_2) + (46180891/1000000000000 : ℝ)*(sp_s0_9) + (254239601/125000000000 : ℝ)*(sp_s0_15) + (182418824061/40000000000 : ℝ)*(sp_s0_21) + (4412685012719/1000000000000 : ℝ)*(sp_s0_22) + (4414576391001/1000000000000 : ℝ)*(sp_s0_23) + (340322814471/200000000000 : ℝ)*(sp_s0_27) + (57730179511/31250000000 : ℝ)*(f.failure) + (4414718929527/1000000000000 : ℝ)*(f.sum) + (1663449080756083/2000000000000000000000000000 : ℝ)*base63 + (1638610208955717/10000000000000000000000000000 : ℝ)*base65 + (1458639374912349/5000000000000000000000000000 : ℝ)*base66 + (5474013595412349/5000000000000000000000000000 : ℝ)*base69 + (942681021156083/2000000000000000000000000000 : ℝ)*base71 + (8292704170955717/10000000000000000000000000000 : ℝ)*base72 + (8499260036955717/10000000000000000000000000000 : ℝ)*base75 + (2070983775587651/5000000000000000000000000000 : ℝ)*base76 + (727306772156083/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1759/1562500000000000 : ℝ)*base86 + (1759/1562500000000000 : ℝ)*base88 + (1759/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (19757/100000 : ℝ) ^ (73/16 : ℝ) ≤ (61196567281492203/100000000000000000000 : ℝ) := by
    have hpowers : (19757/100000 : ℝ)^73 ≤ (61196567281492203/100000000000000000000 : ℝ)^16 := by
      have hnat : (19757 : ℕ)^73*100000000000000000000^16 ≤ 61196567281492203^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19757 100000 61196567281492203 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19757/100000 : ℝ)) (X := (61196567281492203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100061196567281492203/100000000000000000000 : ℝ) ≤ (10001340974282141/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (100061196567281492203/100000000000000000000 : ℝ)^16 ≤ (10001340974282141/10000000000000000 : ℝ)^73 := by
      have hnat : (100061196567281492203 : ℕ)^16*10000000000000000^73 ≤ 10001340974282141^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061196567281492203 100000000000000000000 10001340974282141 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001340974282141/10000000000000000 : ℝ)) (X := (100061196567281492203/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50061196567281492203/50000000000000000000 : ℝ) ≤ (10002681308342923/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (50061196567281492203/50000000000000000000 : ℝ)^16 ≤ (10002681308342923/10000000000000000 : ℝ)^73 := by
      have hnat : (50061196567281492203 : ℕ)^16*10000000000000000^73 ≤ 10002681308342923^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061196567281492203 50000000000000000000 10002681308342923 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002681308342923/10000000000000000 : ℝ)) (X := (50061196567281492203/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1340974282141/1975700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(670167030391/987850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (19757/100000 : ℝ)) (alpha := (1340974282141/1975700000000000 : ℝ)) (beta := (670167030391/987850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19757/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1340974282141/1975700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(670167030391/987850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (26459/50000 : ℝ) ^ (73/16 : ℝ) ≤ (1370504990696633229/25000000000000000000 : ℝ) := by
    have hpowers : (26459/50000 : ℝ)^73 ≤ (1370504990696633229/25000000000000000000 : ℝ)^16 := by
      have hnat : (26459 : ℕ)^73*25000000000000000000^16 ≤ 1370504990696633229^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26459 50000 1370504990696633229 25000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26459/50000 : ℝ)) (X := (1370504990696633229/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26370504990696633229/25000000000000000000 : ℝ) ≤ (10117662901332961/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (26370504990696633229/25000000000000000000 : ℝ)^16 ≤ (10117662901332961/10000000000000000 : ℝ)^73 := by
      have hnat : (26370504990696633229 : ℕ)^16*10000000000000000^73 ≤ 10117662901332961^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26370504990696633229 25000000000000000000 10117662901332961 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10117662901332961/10000000000000000 : ℝ)) (X := (26370504990696633229/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13870504990696633229/12500000000000000000 : ℝ) ≤ (10230643728632647/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (13870504990696633229/12500000000000000000 : ℝ)^16 ≤ (10230643728632647/10000000000000000 : ℝ)^73 := by
      have hnat : (13870504990696633229 : ℕ)^16*10000000000000000^73 ≤ 10230643728632647^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13870504990696633229 12500000000000000000 10230643728632647 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10230643728632647/10000000000000000 : ℝ)) (X := (13870504990696633229/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(117662901332961/5291800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(56490413649843/2645900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (26459/50000 : ℝ)) (alpha := (117662901332961/5291800000000000 : ℝ)) (beta := (56490413649843/2645900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (26459/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(117662901332961/5291800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(56490413649843/2645900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37793/100000 : ℝ) ^ (73/16 : ℝ) ≤ (73759740733409741/6250000000000000000 : ℝ) := by
    have hpowers : (37793/100000 : ℝ)^73 ≤ (73759740733409741/6250000000000000000 : ℝ)^16 := by
      have hnat : (37793 : ℕ)^73*6250000000000000000^16 ≤ 73759740733409741^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37793 100000 73759740733409741 6250000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37793/100000 : ℝ)) (X := (73759740733409741/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6323759740733409741/6250000000000000000 : ℝ) ≤ (2005149615851823/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (6323759740733409741/6250000000000000000 : ℝ)^16 ≤ (2005149615851823/2000000000000000 : ℝ)^73 := by
      have hnat : (6323759740733409741 : ℕ)^16*2000000000000000^73 ≤ 2005149615851823^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6323759740733409741 6250000000000000000 2005149615851823 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005149615851823/2000000000000000 : ℝ)) (X := (6323759740733409741/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3198759740733409741/3125000000000000000 : ℝ) ≤ (5025631358437871/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3198759740733409741/3125000000000000000 : ℝ)^16 ≤ (5025631358437871/5000000000000000 : ℝ)^73 := by
      have hnat : (3198759740733409741 : ℕ)^16*5000000000000000^73 ≤ 5025631358437871^73*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3198759740733409741 3125000000000000000 5025631358437871 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025631358437871/5000000000000000 : ℝ)) (X := (3198759740733409741/3125000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(5149615851823/755860000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25514637616627/3779300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (37793/100000 : ℝ)) (alpha := (5149615851823/755860000000000 : ℝ)) (beta := (25514637616627/3779300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37793/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(5149615851823/755860000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25514637616627/3779300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-114405353/500000000 : ℝ)*X 0 0+(-301496931/625000000 : ℝ)*X 0 1+(-1075478343/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6199945803/10000000000 : ℝ)*X 1 0+(10316441/31250000 : ℝ)*X 1 1+(-2980551303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2094051981/5000000000 : ℝ)*X 2 0+(-4461721919/10000000000 : ℝ)*X 2 1+(4028276041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((981394477/2500000000 : ℝ)*X 0 0+(-2068269279/5000000000 : ℝ)*X 0 1+(-4611114137/10000000000 : ℝ)*X 0 2+(981394477/2500000000 : ℝ)*X 1 0+(-2068269279/5000000000 : ℝ)*X 1 1+(-4611114137/10000000000 : ℝ)*X 1 2+(981394477/2500000000 : ℝ)*X 2 0+(-2068269279/5000000000 : ℝ)*X 2 1+(-4611114137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-358461/50000 : ℝ) < ((-169487/100000 : ℝ)*P 0+(-169487/100000 : ℝ)*P 1+(-169487/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-358461/50000 : ℝ) < (-304645495494743391983939554438465431/42948496191650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3859/500000000000 : ℝ)*(base21) + (18825121391/25000000000 : ℝ)*(base39) + (56281272019/250000000000 : ℝ)*(base40) + (16807/1000000000000 : ℝ)*(base43) + (68970169143/250000000000 : ℝ)*(base49) + (6819/1000000000000 : ℝ)*(base59) + (30414291983/200000000000 : ℝ)*(base60) + (169487/100000 : ℝ)*(major_s1_0) + (1694869983193/1000000000000 : ℝ)*(major_s1_1) + (169487/100000 : ℝ)*(major_s1_2) + (591106246649/250000000000 : ℝ)*(sp_s1_0) + (2364425003403/1000000000000 : ℝ)*(sp_s1_1) + (2364424981719/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2364425003403/1000000000000 : ℝ)*(f.sum) + (866178763974989893/99996498700000000000000000000000 : ℝ)*base63 + (1502511732229/2952578125000000000000000 : ℝ)*base64 + (608967223479273/5291800000000000000000000000 : ℝ)*base66 + (126832616646937/377930000000000000000000000 : ℝ)*base68 + (607966470414451/1014505843750000000000000000 : ℝ)*base70 + (2112299249631/8590000000000000000000000 : ℝ)*base73 + (1830326876219281/2645900000000000000000000000 : ℝ)*base75 + (24404779667335699/8590000000000000000000000 : ℝ)*base77 + (859135981774665713/4545656200000000000000000000000 : ℝ)*base79 + (2841/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p013_b027 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 := by omega
  rcases hc with rfl
  · exact collision_c313068 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
