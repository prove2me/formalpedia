-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:53.522013+00:00
-- url     : https://prove2.me/submissions/100e1ec4-c455-4071-89e7-3d595815adcc

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
theorem collision_support_c326045_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1569/2000000000 : ℝ)*x 0 + (-1599187241/2500000000 : ℝ)*x 1 + (4908825933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1569/2000000000 : ℝ)^89 ≤ (3600987/100000000000000 : ℝ)^73 := by
    have hnat : (1569 : ℕ)^89*100000000000000^73 ≤ 3600987^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569 2000000000 3600987 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1599187241/2500000000 : ℝ)^89 ≤ (58000246673221/100000000000000 : ℝ)^73 := by
    have hnat : (1599187241 : ℕ)^89*100000000000000^73 ≤ 58000246673221^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599187241 2500000000 58000246673221 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4908825933/10000000000 : ℝ)^89 ≤ (41999749717049/100000000000000 : ℝ)^73 := by
    have hnat : (4908825933 : ℕ)^89*100000000000000^73 ≤ 41999749717049^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908825933 10000000000 41999749717049 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1569/2000000000 : ℝ), (-1599187241/2500000000 : ℝ), (4908825933/10000000000 : ℝ)] ![(3600987/100000000000000 : ℝ), (58000246673221/100000000000000 : ℝ), (41999749717049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1569/2000000000 : ℝ)|^89 ≤ (3600987/100000000000000 : ℝ)^73
        have hw : |(1569/2000000000 : ℝ)|=(1569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1599187241/2500000000 : ℝ)|^89 ≤ (58000246673221/100000000000000 : ℝ)^73
        have hw : |(-1599187241/2500000000 : ℝ)|=(1599187241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4908825933/10000000000 : ℝ)|^89 ≤ (41999749717049/100000000000000 : ℝ)^73
        have hw : |(4908825933/10000000000 : ℝ)|=(4908825933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1332455181/2500000000 : ℝ)*x 0 + (408092067/1250000000 : ℝ)*x 1 + (44031263/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1332455181/2500000000 : ℝ)^89 ≤ (23215818378347/50000000000000 : ℝ)^73 := by
    have hnat : (1332455181 : ℕ)^89*50000000000000^73 ≤ 23215818378347^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332455181 2500000000 23215818378347 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408092067/1250000000 : ℝ)^89 ≤ (5108863540897/20000000000000 : ℝ)^73 := by
    have hnat : (408092067 : ℕ)^89*20000000000000^73 ≤ 5108863540897^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408092067 1250000000 5108863540897 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44031263/125000000 : ℝ)^89 ≤ (28024045519257/100000000000000 : ℝ)^73 := by
    have hnat : (44031263 : ℕ)^89*100000000000000^73 ≤ 28024045519257^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44031263 125000000 28024045519257 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1332455181/2500000000 : ℝ), (408092067/1250000000 : ℝ), (44031263/125000000 : ℝ)] ![(23215818378347/50000000000000 : ℝ), (5108863540897/20000000000000 : ℝ), (28024045519257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1332455181/2500000000 : ℝ)|^89 ≤ (23215818378347/50000000000000 : ℝ)^73
        have hw : |(1332455181/2500000000 : ℝ)|=(1332455181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(408092067/1250000000 : ℝ)|^89 ≤ (5108863540897/20000000000000 : ℝ)^73
        have hw : |(408092067/1250000000 : ℝ)|=(408092067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44031263/125000000 : ℝ)|^89 ≤ (28024045519257/100000000000000 : ℝ)^73
        have hw : |(44031263/125000000 : ℝ)|=(44031263/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5877649863/10000000000 : ℝ)*x 0 + (-2939508491/10000000000 : ℝ)*x 1 + (-3229573129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5877649863/10000000000 : ℝ)^89 ≤ (10462807111319/20000000000000 : ℝ)^73 := by
    have hnat : (5877649863 : ℕ)^89*20000000000000^73 ≤ 10462807111319^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5877649863 10000000000 10462807111319 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939508491/10000000000 : ℝ)^89 ≤ (22476681505989/100000000000000 : ℝ)^73 := by
    have hnat : (2939508491 : ℕ)^89*100000000000000^73 ≤ 22476681505989^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939508491 10000000000 22476681505989 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3229573129/10000000000 : ℝ)^89 ≤ (6302320730913/25000000000000 : ℝ)^73 := by
    have hnat : (3229573129 : ℕ)^89*25000000000000^73 ≤ 6302320730913^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229573129 10000000000 6302320730913 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5877649863/10000000000 : ℝ), (-2939508491/10000000000 : ℝ), (-3229573129/10000000000 : ℝ)] ![(10462807111319/20000000000000 : ℝ), (22476681505989/100000000000000 : ℝ), (6302320730913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5877649863/10000000000 : ℝ)|^89 ≤ (10462807111319/20000000000000 : ℝ)^73
        have hw : |(5877649863/10000000000 : ℝ)|=(5877649863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2939508491/10000000000 : ℝ)|^89 ≤ (22476681505989/100000000000000 : ℝ)^73
        have hw : |(-2939508491/10000000000 : ℝ)|=(2939508491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3229573129/10000000000 : ℝ)|^89 ≤ (6302320730913/25000000000000 : ℝ)^73
        have hw : |(-3229573129/10000000000 : ℝ)|=(3229573129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (84347193/156250000 : ℝ)*x 0 + (-2260553941/10000000000 : ℝ)*x 1 + (4377263489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84347193/156250000 : ℝ)^89 ≤ (47159132764437/100000000000000 : ℝ)^73 := by
    have hnat : (84347193 : ℕ)^89*100000000000000^73 ≤ 47159132764437^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84347193 156250000 47159132764437 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260553941/10000000000 : ℝ)^89 ≤ (8159112730349/50000000000000 : ℝ)^73 := by
    have hnat : (2260553941 : ℕ)^89*50000000000000^73 ≤ 8159112730349^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260553941 10000000000 8159112730349 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4377263489/10000000000 : ℝ)^89 ≤ (36522641753133/100000000000000 : ℝ)^73 := by
    have hnat : (4377263489 : ℕ)^89*100000000000000^73 ≤ 36522641753133^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377263489 10000000000 36522641753133 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84347193/156250000 : ℝ), (-2260553941/10000000000 : ℝ), (4377263489/10000000000 : ℝ)] ![(47159132764437/100000000000000 : ℝ), (8159112730349/50000000000000 : ℝ), (36522641753133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84347193/156250000 : ℝ)|^89 ≤ (47159132764437/100000000000000 : ℝ)^73
        have hw : |(84347193/156250000 : ℝ)|=(84347193/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260553941/10000000000 : ℝ)|^89 ≤ (8159112730349/50000000000000 : ℝ)^73
        have hw : |(-2260553941/10000000000 : ℝ)|=(2260553941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4377263489/10000000000 : ℝ)|^89 ≤ (36522641753133/100000000000000 : ℝ)^73
        have hw : |(4377263489/10000000000 : ℝ)|=(4377263489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7/500000000 : ℝ)*x 0 + (-839496857/1000000000 : ℝ)*x 1 + (103362603/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7/500000000 : ℝ)^89 ≤ (26591/100000000000000 : ℝ)^73 := by
    have hnat : (7 : ℕ)^89*100000000000000^73 ≤ 26591^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7 500000000 26591 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (839496857/1000000000 : ℝ)^89 ≤ (80791509215127/100000000000000 : ℝ)^73 := by
    have hnat : (839496857 : ℕ)^89*100000000000000^73 ≤ 80791509215127^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839496857 1000000000 80791509215127 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103362603/400000000 : ℝ)^89 ≤ (150066333999/781250000000 : ℝ)^73 := by
    have hnat : (103362603 : ℕ)^89*781250000000^73 ≤ 150066333999^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103362603 400000000 150066333999 781250000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7/500000000 : ℝ), (-839496857/1000000000 : ℝ), (103362603/400000000 : ℝ)] ![(26591/100000000000000 : ℝ), (80791509215127/100000000000000 : ℝ), (150066333999/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7/500000000 : ℝ)|^89 ≤ (26591/100000000000000 : ℝ)^73
        have hw : |(7/500000000 : ℝ)|=(7/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-839496857/1000000000 : ℝ)|^89 ≤ (80791509215127/100000000000000 : ℝ)^73
        have hw : |(-839496857/1000000000 : ℝ)|=(839496857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103362603/400000000 : ℝ)|^89 ≤ (150066333999/781250000000 : ℝ)^73
        have hw : |(103362603/400000000 : ℝ)|=(103362603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1697655003/5000000000 : ℝ)*x 0 + (4572366403/10000000000 : ℝ)*x 1 + (167842381/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697655003/5000000000 : ℝ)^89 ≤ (6698822893681/25000000000000 : ℝ)^73 := by
    have hnat : (1697655003 : ℕ)^89*25000000000000^73 ≤ 6698822893681^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697655003 5000000000 6698822893681 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572366403/10000000000 : ℝ)^89 ≤ (9629226342873/25000000000000 : ℝ)^73 := by
    have hnat : (4572366403 : ℕ)^89*25000000000000^73 ≤ 9629226342873^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572366403 10000000000 9629226342873 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167842381/400000000 : ℝ)^89 ≤ (693756060691/2000000000000 : ℝ)^73 := by
    have hnat : (167842381 : ℕ)^89*2000000000000^73 ≤ 693756060691^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167842381 400000000 693756060691 2000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1697655003/5000000000 : ℝ), (4572366403/10000000000 : ℝ), (167842381/400000000 : ℝ)] ![(6698822893681/25000000000000 : ℝ), (9629226342873/25000000000000 : ℝ), (693756060691/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1697655003/5000000000 : ℝ)|^89 ≤ (6698822893681/25000000000000 : ℝ)^73
        have hw : |(1697655003/5000000000 : ℝ)|=(1697655003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572366403/10000000000 : ℝ)|^89 ≤ (9629226342873/25000000000000 : ℝ)^73
        have hw : |(4572366403/10000000000 : ℝ)|=(4572366403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(167842381/400000000 : ℝ)|^89 ≤ (693756060691/2000000000000 : ℝ)^73
        have hw : |(167842381/400000000 : ℝ)|=(167842381/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5007304381/10000000000 : ℝ)*x 0 + (-1272490313/5000000000 : ℝ)*x 1 + (-90665643/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5007304381/10000000000 : ℝ)^89 ≤ (10757312363031/25000000000000 : ℝ)^73 := by
    have hnat : (5007304381 : ℕ)^89*25000000000000^73 ≤ 10757312363031^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007304381 10000000000 10757312363031 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272490313/5000000000 : ℝ)^89 ≤ (9427435052161/50000000000000 : ℝ)^73 := by
    have hnat : (1272490313 : ℕ)^89*50000000000000^73 ≤ 9427435052161^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272490313 5000000000 9427435052161 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90665643/200000000 : ℝ)^89 ≤ (7623176084057/20000000000000 : ℝ)^73 := by
    have hnat : (90665643 : ℕ)^89*20000000000000^73 ≤ 7623176084057^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90665643 200000000 7623176084057 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5007304381/10000000000 : ℝ), (-1272490313/5000000000 : ℝ), (-90665643/200000000 : ℝ)] ![(10757312363031/25000000000000 : ℝ), (9427435052161/50000000000000 : ℝ), (7623176084057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5007304381/10000000000 : ℝ)|^89 ≤ (10757312363031/25000000000000 : ℝ)^73
        have hw : |(5007304381/10000000000 : ℝ)|=(5007304381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1272490313/5000000000 : ℝ)|^89 ≤ (9427435052161/50000000000000 : ℝ)^73
        have hw : |(-1272490313/5000000000 : ℝ)|=(1272490313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90665643/200000000 : ℝ)|^89 ≤ (7623176084057/20000000000000 : ℝ)^73
        have hw : |(-90665643/200000000 : ℝ)|=(90665643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (524332041/1000000000 : ℝ)*x 0 + (-26667437/2000000000 : ℝ)*x 1 + (3014815199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524332041/1000000000 : ℝ)^89 ≤ (9102910255521/20000000000000 : ℝ)^73 := by
    have hnat : (524332041 : ℕ)^89*20000000000000^73 ≤ 9102910255521^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524332041 1000000000 9102910255521 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26667437/2000000000 : ℝ)^89 ≤ (258792510989/50000000000000 : ℝ)^73 := by
    have hnat : (26667437 : ℕ)^89*50000000000000^73 ≤ 258792510989^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26667437 2000000000 258792510989 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014815199/5000000000 : ℝ)^89 ≤ (26983931844433/50000000000000 : ℝ)^73 := by
    have hnat : (3014815199 : ℕ)^89*50000000000000^73 ≤ 26983931844433^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014815199 5000000000 26983931844433 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524332041/1000000000 : ℝ), (-26667437/2000000000 : ℝ), (3014815199/5000000000 : ℝ)] ![(9102910255521/20000000000000 : ℝ), (258792510989/50000000000000 : ℝ), (26983931844433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524332041/1000000000 : ℝ)|^89 ≤ (9102910255521/20000000000000 : ℝ)^73
        have hw : |(524332041/1000000000 : ℝ)|=(524332041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26667437/2000000000 : ℝ)|^89 ≤ (258792510989/50000000000000 : ℝ)^73
        have hw : |(-26667437/2000000000 : ℝ)|=(26667437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014815199/5000000000 : ℝ)|^89 ≤ (26983931844433/50000000000000 : ℝ)^73
        have hw : |(3014815199/5000000000 : ℝ)|=(3014815199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (198739/10000000000 : ℝ)*x 0 + (-282032213/625000000 : ℝ)*x 1 + (3382514873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198739/10000000000 : ℝ)^89 ≤ (37050989/20000000000000 : ℝ)^73 := by
    have hnat : (198739 : ℕ)^89*20000000000000^73 ≤ 37050989^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198739 10000000000 37050989 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282032213/625000000 : ℝ)^89 ≤ (18951555213787/50000000000000 : ℝ)^73 := by
    have hnat : (282032213 : ℕ)^89*50000000000000^73 ≤ 18951555213787^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282032213 625000000 18951555213787 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3382514873/5000000000 : ℝ)^89 ≤ (31048352151547/50000000000000 : ℝ)^73 := by
    have hnat : (3382514873 : ℕ)^89*50000000000000^73 ≤ 31048352151547^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3382514873 5000000000 31048352151547 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(198739/10000000000 : ℝ), (-282032213/625000000 : ℝ), (3382514873/5000000000 : ℝ)] ![(37050989/20000000000000 : ℝ), (18951555213787/50000000000000 : ℝ), (31048352151547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(198739/10000000000 : ℝ)|^89 ≤ (37050989/20000000000000 : ℝ)^73
        have hw : |(198739/10000000000 : ℝ)|=(198739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282032213/625000000 : ℝ)|^89 ≤ (18951555213787/50000000000000 : ℝ)^73
        have hw : |(-282032213/625000000 : ℝ)|=(282032213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3382514873/5000000000 : ℝ)|^89 ≤ (31048352151547/50000000000000 : ℝ)^73
        have hw : |(3382514873/5000000000 : ℝ)|=(3382514873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2173578821/10000000000 : ℝ)*x 0 + (1841749369/5000000000 : ℝ)*x 1 + (152760183/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173578821/10000000000 : ℝ)^89 ≤ (7778014922741/50000000000000 : ℝ)^73 := by
    have hnat : (2173578821 : ℕ)^89*50000000000000^73 ≤ 7778014922741^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173578821 10000000000 7778014922741 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1841749369/5000000000 : ℝ)^89 ≤ (29593364215869/100000000000000 : ℝ)^73 := by
    have hnat : (1841749369 : ℕ)^89*100000000000000^73 ≤ 29593364215869^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841749369 5000000000 29593364215869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152760183/250000000 : ℝ)^89 ≤ (10970121185313/20000000000000 : ℝ)^73 := by
    have hnat : (152760183 : ℕ)^89*20000000000000^73 ≤ 10970121185313^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152760183 250000000 10970121185313 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173578821/10000000000 : ℝ), (1841749369/5000000000 : ℝ), (152760183/250000000 : ℝ)] ![(7778014922741/50000000000000 : ℝ), (29593364215869/100000000000000 : ℝ), (10970121185313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173578821/10000000000 : ℝ)|^89 ≤ (7778014922741/50000000000000 : ℝ)^73
        have hw : |(2173578821/10000000000 : ℝ)|=(2173578821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1841749369/5000000000 : ℝ)|^89 ≤ (29593364215869/100000000000000 : ℝ)^73
        have hw : |(1841749369/5000000000 : ℝ)|=(1841749369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152760183/250000000 : ℝ)|^89 ≤ (10970121185313/20000000000000 : ℝ)^73
        have hw : |(152760183/250000000 : ℝ)|=(152760183/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3955630653/5000000000 : ℝ)*x 0 + (-168809427/1250000000 : ℝ)*x 1 + (-2240249137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3955630653/5000000000 : ℝ)^89 ≤ (7515249847109/10000000000000 : ℝ)^73 := by
    have hnat : (3955630653 : ℕ)^89*10000000000000^73 ≤ 7515249847109^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955630653 5000000000 7515249847109 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168809427/1250000000 : ℝ)^89 ≤ (544237469609/6250000000000 : ℝ)^73 := by
    have hnat : (168809427 : ℕ)^89*6250000000000^73 ≤ 544237469609^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168809427 1250000000 544237469609 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240249137/10000000000 : ℝ)^89 ≤ (16139702003477/100000000000000 : ℝ)^73 := by
    have hnat : (2240249137 : ℕ)^89*100000000000000^73 ≤ 16139702003477^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240249137 10000000000 16139702003477 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3955630653/5000000000 : ℝ), (-168809427/1250000000 : ℝ), (-2240249137/10000000000 : ℝ)] ![(7515249847109/10000000000000 : ℝ), (544237469609/6250000000000 : ℝ), (16139702003477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3955630653/5000000000 : ℝ)|^89 ≤ (7515249847109/10000000000000 : ℝ)^73
        have hw : |(3955630653/5000000000 : ℝ)|=(3955630653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168809427/1250000000 : ℝ)|^89 ≤ (544237469609/6250000000000 : ℝ)^73
        have hw : |(-168809427/1250000000 : ℝ)|=(168809427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2240249137/10000000000 : ℝ)|^89 ≤ (16139702003477/100000000000000 : ℝ)^73
        have hw : |(-2240249137/10000000000 : ℝ)|=(2240249137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_17 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^89 ≤ (1 : ℝ)^73 := by
    have hnat : (1 : ℕ)^89*1^73 ≤ 1^73*1^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^89 ≤ (0 : ℝ)^73 := by
    have hnat : (0 : ℕ)^89*1^73 ≤ 0^73*1^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^89 ≤ (0 : ℝ)^73 := by
    have hnat : (0 : ℕ)^89*1^73 ≤ 0^73*1^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^89 ≤ (1 : ℝ)^73
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^89 ≤ (0 : ℝ)^73
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^89 ≤ (0 : ℝ)^73
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (713758859/1000000000 : ℝ)*x 0 + (-369910817/2000000000 : ℝ)*x 1 + (1386398413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (713758859/1000000000 : ℝ)^89 ≤ (33145396389609/50000000000000 : ℝ)^73 := by
    have hnat : (713758859 : ℕ)^89*50000000000000^73 ≤ 33145396389609^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713758859 1000000000 33145396389609 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369910817/2000000000 : ℝ)^89 ≤ (63884308519/500000000000 : ℝ)^73 := by
    have hnat : (369910817 : ℕ)^89*500000000000^73 ≤ 63884308519^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369910817 2000000000 63884308519 500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386398413/5000000000 : ℝ)^89 ≤ (10466172750641/50000000000000 : ℝ)^73 := by
    have hnat : (1386398413 : ℕ)^89*50000000000000^73 ≤ 10466172750641^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386398413 5000000000 10466172750641 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(713758859/1000000000 : ℝ), (-369910817/2000000000 : ℝ), (1386398413/5000000000 : ℝ)] ![(33145396389609/50000000000000 : ℝ), (63884308519/500000000000 : ℝ), (10466172750641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(713758859/1000000000 : ℝ)|^89 ≤ (33145396389609/50000000000000 : ℝ)^73
        have hw : |(713758859/1000000000 : ℝ)|=(713758859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369910817/2000000000 : ℝ)|^89 ≤ (63884308519/500000000000 : ℝ)^73
        have hw : |(-369910817/2000000000 : ℝ)|=(369910817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1386398413/5000000000 : ℝ)|^89 ≤ (10466172750641/50000000000000 : ℝ)^73
        have hw : |(1386398413/5000000000 : ℝ)|=(1386398413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (14773/5000000000 : ℝ)*x 0 + (-2171319859/2500000000 : ℝ)*x 1 + (2200291433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14773/5000000000 : ℝ)^89 ≤ (18136489/100000000000000 : ℝ)^73 := by
    have hnat : (14773 : ℕ)^89*100000000000000^73 ≤ 18136489^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14773 5000000000 18136489 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171319859/2500000000 : ℝ)^89 ≤ (84210558086333/100000000000000 : ℝ)^73 := by
    have hnat : (2171319859 : ℕ)^89*100000000000000^73 ≤ 84210558086333^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171319859 2500000000 84210558086333 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200291433/10000000000 : ℝ)^89 ≤ (3947355941497/25000000000000 : ℝ)^73 := by
    have hnat : (2200291433 : ℕ)^89*25000000000000^73 ≤ 3947355941497^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200291433 10000000000 3947355941497 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14773/5000000000 : ℝ), (-2171319859/2500000000 : ℝ), (2200291433/10000000000 : ℝ)] ![(18136489/100000000000000 : ℝ), (84210558086333/100000000000000 : ℝ), (3947355941497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14773/5000000000 : ℝ)|^89 ≤ (18136489/100000000000000 : ℝ)^73
        have hw : |(14773/5000000000 : ℝ)|=(14773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171319859/2500000000 : ℝ)|^89 ≤ (84210558086333/100000000000000 : ℝ)^73
        have hw : |(-2171319859/2500000000 : ℝ)|=(2171319859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200291433/10000000000 : ℝ)|^89 ≤ (3947355941497/25000000000000 : ℝ)^73
        have hw : |(2200291433/10000000000 : ℝ)|=(2200291433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1501140871/2000000000 : ℝ)*x 0 + (281307017/1250000000 : ℝ)*x 1 + (1910065653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1501140871/2000000000 : ℝ)^89 ≤ (35241143831711/50000000000000 : ℝ)^73 := by
    have hnat : (1501140871 : ℕ)^89*50000000000000^73 ≤ 35241143831711^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501140871 2000000000 35241143831711 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281307017/1250000000 : ℝ)^89 ≤ (16229399629331/100000000000000 : ℝ)^73 := by
    have hnat : (281307017 : ℕ)^89*100000000000000^73 ≤ 16229399629331^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281307017 1250000000 16229399629331 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910065653/10000000000 : ℝ)^89 ≤ (13288312696923/100000000000000 : ℝ)^73 := by
    have hnat : (1910065653 : ℕ)^89*100000000000000^73 ≤ 13288312696923^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910065653 10000000000 13288312696923 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1501140871/2000000000 : ℝ), (281307017/1250000000 : ℝ), (1910065653/10000000000 : ℝ)] ![(35241143831711/50000000000000 : ℝ), (16229399629331/100000000000000 : ℝ), (13288312696923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1501140871/2000000000 : ℝ)|^89 ≤ (35241143831711/50000000000000 : ℝ)^73
        have hw : |(1501140871/2000000000 : ℝ)|=(1501140871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281307017/1250000000 : ℝ)|^89 ≤ (16229399629331/100000000000000 : ℝ)^73
        have hw : |(281307017/1250000000 : ℝ)|=(281307017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1910065653/10000000000 : ℝ)|^89 ≤ (13288312696923/100000000000000 : ℝ)^73
        have hw : |(1910065653/10000000000 : ℝ)|=(1910065653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2556187627/10000000000 : ℝ)*x 0 + (-5401592203/10000000000 : ℝ)*x 1 + (-2056315907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2556187627/10000000000 : ℝ)^89 ≤ (18956145725217/100000000000000 : ℝ)^73 := by
    have hnat : (2556187627 : ℕ)^89*100000000000000^73 ≤ 18956145725217^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556187627 10000000000 18956145725217 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401592203/10000000000 : ℝ)^89 ≤ (4719504814279/10000000000000 : ℝ)^73 := by
    have hnat : (5401592203 : ℕ)^89*10000000000000^73 ≤ 4719504814279^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401592203 10000000000 4719504814279 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056315907/5000000000 : ℝ)^89 ≤ (16924403060023/50000000000000 : ℝ)^73 := by
    have hnat : (2056315907 : ℕ)^89*50000000000000^73 ≤ 16924403060023^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056315907 5000000000 16924403060023 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2556187627/10000000000 : ℝ), (-5401592203/10000000000 : ℝ), (-2056315907/5000000000 : ℝ)] ![(18956145725217/100000000000000 : ℝ), (4719504814279/10000000000000 : ℝ), (16924403060023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2556187627/10000000000 : ℝ)|^89 ≤ (18956145725217/100000000000000 : ℝ)^73
        have hw : |(2556187627/10000000000 : ℝ)|=(2556187627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5401592203/10000000000 : ℝ)|^89 ≤ (4719504814279/10000000000000 : ℝ)^73
        have hw : |(-5401592203/10000000000 : ℝ)|=(5401592203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056315907/5000000000 : ℝ)|^89 ≤ (16924403060023/50000000000000 : ℝ)^73
        have hw : |(-2056315907/5000000000 : ℝ)|=(2056315907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (93691801/125000000 : ℝ)*x 0 + (-23554087/250000000 : ℝ)*x 1 + (3104301801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93691801/125000000 : ℝ)^89 ≤ (703636940657/1000000000000 : ℝ)^73 := by
    have hnat : (93691801 : ℕ)^89*1000000000000^73 ≤ 703636940657^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93691801 125000000 703636940657 1000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23554087/250000000 : ℝ)^89 ≤ (2807031155623/50000000000000 : ℝ)^73 := by
    have hnat : (23554087 : ℕ)^89*50000000000000^73 ≤ 2807031155623^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23554087 250000000 2807031155623 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3104301801/10000000000 : ℝ)^89 ≤ (24022243610487/100000000000000 : ℝ)^73 := by
    have hnat : (3104301801 : ℕ)^89*100000000000000^73 ≤ 24022243610487^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104301801 10000000000 24022243610487 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(93691801/125000000 : ℝ), (-23554087/250000000 : ℝ), (3104301801/10000000000 : ℝ)] ![(703636940657/1000000000000 : ℝ), (2807031155623/50000000000000 : ℝ), (24022243610487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(93691801/125000000 : ℝ)|^89 ≤ (703636940657/1000000000000 : ℝ)^73
        have hw : |(93691801/125000000 : ℝ)|=(93691801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23554087/250000000 : ℝ)|^89 ≤ (2807031155623/50000000000000 : ℝ)^73
        have hw : |(-23554087/250000000 : ℝ)|=(23554087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3104301801/10000000000 : ℝ)|^89 ≤ (24022243610487/100000000000000 : ℝ)^73
        have hw : |(3104301801/10000000000 : ℝ)|=(3104301801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-904293779/10000000000 : ℝ)*x 0 + (-1368569503/2500000000 : ℝ)*x 1 + (5354074951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904293779/10000000000 : ℝ)^89 ≤ (5340174768119/100000000000000 : ℝ)^73 := by
    have hnat : (904293779 : ℕ)^89*100000000000000^73 ≤ 5340174768119^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904293779 10000000000 5340174768119 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368569503/2500000000 : ℝ)^89 ≤ (47970454143881/100000000000000 : ℝ)^73 := by
    have hnat : (1368569503 : ℕ)^89*100000000000000^73 ≤ 47970454143881^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368569503 2500000000 47970454143881 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5354074951/10000000000 : ℝ)^89 ≤ (23344685537553/50000000000000 : ℝ)^73 := by
    have hnat : (5354074951 : ℕ)^89*50000000000000^73 ≤ 23344685537553^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354074951 10000000000 23344685537553 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904293779/10000000000 : ℝ), (-1368569503/2500000000 : ℝ), (5354074951/10000000000 : ℝ)] ![(5340174768119/100000000000000 : ℝ), (47970454143881/100000000000000 : ℝ), (23344685537553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904293779/10000000000 : ℝ)|^89 ≤ (5340174768119/100000000000000 : ℝ)^73
        have hw : |(-904293779/10000000000 : ℝ)|=(904293779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368569503/2500000000 : ℝ)|^89 ≤ (47970454143881/100000000000000 : ℝ)^73
        have hw : |(-1368569503/2500000000 : ℝ)|=(1368569503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5354074951/10000000000 : ℝ)|^89 ≤ (23344685537553/50000000000000 : ℝ)^73
        have hw : |(5354074951/10000000000 : ℝ)|=(5354074951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5379387301/10000000000 : ℝ)*x 0 + (667699221/2000000000 : ℝ)*x 1 + (678987727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379387301/10000000000 : ℝ)^89 ≤ (1878344896401/4000000000000 : ℝ)^73 := by
    have hnat : (5379387301 : ℕ)^89*4000000000000^73 ≤ 1878344896401^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379387301 10000000000 1878344896401 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667699221/2000000000 : ℝ)^89 ≤ (820301847799/3125000000000 : ℝ)^73 := by
    have hnat : (667699221 : ℕ)^89*3125000000000^73 ≤ 820301847799^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667699221 2000000000 820301847799 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678987727/2000000000 : ℝ)^89 ≤ (6697929610843/25000000000000 : ℝ)^73 := by
    have hnat : (678987727 : ℕ)^89*25000000000000^73 ≤ 6697929610843^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678987727 2000000000 6697929610843 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379387301/10000000000 : ℝ), (667699221/2000000000 : ℝ), (678987727/2000000000 : ℝ)] ![(1878344896401/4000000000000 : ℝ), (820301847799/3125000000000 : ℝ), (6697929610843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379387301/10000000000 : ℝ)|^89 ≤ (1878344896401/4000000000000 : ℝ)^73
        have hw : |(5379387301/10000000000 : ℝ)|=(5379387301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667699221/2000000000 : ℝ)|^89 ≤ (820301847799/3125000000000 : ℝ)^73
        have hw : |(667699221/2000000000 : ℝ)|=(667699221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678987727/2000000000 : ℝ)|^89 ≤ (6697929610843/25000000000000 : ℝ)^73
        have hw : |(678987727/2000000000 : ℝ)|=(678987727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167526419/312500000 : ℝ)*x 0 + (-133942623/400000000 : ℝ)*x 1 + (-425675201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167526419/312500000 : ℝ)^89 ≤ (9352272436981/20000000000000 : ℝ)^73 := by
    have hnat : (167526419 : ℕ)^89*20000000000000^73 ≤ 9352272436981^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167526419 312500000 9352272436981 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133942623/400000000 : ℝ)^89 ≤ (6586554377249/25000000000000 : ℝ)^73 := by
    have hnat : (133942623 : ℕ)^89*25000000000000^73 ≤ 6586554377249^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133942623 400000000 6586554377249 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425675201/1250000000 : ℝ)^89 ≤ (1075696811577/4000000000000 : ℝ)^73 := by
    have hnat : (425675201 : ℕ)^89*4000000000000^73 ≤ 1075696811577^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425675201 1250000000 1075696811577 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167526419/312500000 : ℝ), (-133942623/400000000 : ℝ), (-425675201/1250000000 : ℝ)] ![(9352272436981/20000000000000 : ℝ), (6586554377249/25000000000000 : ℝ), (1075696811577/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167526419/312500000 : ℝ)|^89 ≤ (9352272436981/20000000000000 : ℝ)^73
        have hw : |(167526419/312500000 : ℝ)|=(167526419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133942623/400000000 : ℝ)|^89 ≤ (6586554377249/25000000000000 : ℝ)^73
        have hw : |(-133942623/400000000 : ℝ)|=(133942623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425675201/1250000000 : ℝ)|^89 ≤ (1075696811577/4000000000000 : ℝ)^73
        have hw : |(-425675201/1250000000 : ℝ)|=(425675201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326045_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1021728031/2000000000 : ℝ)*x 0 + (-700892439/2000000000 : ℝ)*x 1 + (705191209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021728031/2000000000 : ℝ)^89 ≤ (8818652433057/20000000000000 : ℝ)^73 := by
    have hnat : (1021728031 : ℕ)^89*20000000000000^73 ≤ 8818652433057^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021728031 2000000000 8818652433057 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700892439/2000000000 : ℝ)^89 ≤ (556983541479/2000000000000 : ℝ)^73 := by
    have hnat : (700892439 : ℕ)^89*2000000000000^73 ≤ 556983541479^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700892439 2000000000 556983541479 2000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705191209/2000000000 : ℝ)^89 ≤ (7014390187119/25000000000000 : ℝ)^73 := by
    have hnat : (705191209 : ℕ)^89*25000000000000^73 ≤ 7014390187119^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705191209 2000000000 7014390187119 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021728031/2000000000 : ℝ), (-700892439/2000000000 : ℝ), (705191209/2000000000 : ℝ)] ![(8818652433057/20000000000000 : ℝ), (556983541479/2000000000000 : ℝ), (7014390187119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021728031/2000000000 : ℝ)|^89 ≤ (8818652433057/20000000000000 : ℝ)^73
        have hw : |(1021728031/2000000000 : ℝ)|=(1021728031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700892439/2000000000 : ℝ)|^89 ≤ (556983541479/2000000000000 : ℝ)^73
        have hw : |(-700892439/2000000000 : ℝ)|=(700892439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705191209/2000000000 : ℝ)|^89 ≤ (7014390187119/25000000000000 : ℝ)^73
        have hw : |(705191209/2000000000 : ℝ)|=(705191209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326045 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((1569/2000000000 : ℝ)*X 0 0+(-1599187241/2500000000 : ℝ)*X 0 1+(4908825933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1332455181/2500000000 : ℝ)*X 1 0+(408092067/1250000000 : ℝ)*X 1 1+(44031263/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5877649863/10000000000 : ℝ)*X 2 0+(-2939508491/10000000000 : ℝ)*X 2 1+(-3229573129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((84347193/156250000 : ℝ)*X 0 0+(-2260553941/10000000000 : ℝ)*X 0 1+(4377263489/10000000000 : ℝ)*X 0 2+(84347193/156250000 : ℝ)*X 1 0+(-2260553941/10000000000 : ℝ)*X 1 1+(4377263489/10000000000 : ℝ)*X 1 2+(84347193/156250000 : ℝ)*X 2 0+(-2260553941/10000000000 : ℝ)*X 2 1+(4377263489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((7/500000000 : ℝ)*X 0 0+(-839496857/1000000000 : ℝ)*X 0 1+(103362603/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1697655003/5000000000 : ℝ)*X 1 0+(4572366403/10000000000 : ℝ)*X 1 1+(167842381/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5007304381/10000000000 : ℝ)*X 2 0+(-1272490313/5000000000 : ℝ)*X 2 1+(-90665643/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((524332041/1000000000 : ℝ)*X 0 0+(-26667437/2000000000 : ℝ)*X 0 1+(3014815199/5000000000 : ℝ)*X 0 2+(524332041/1000000000 : ℝ)*X 1 0+(-26667437/2000000000 : ℝ)*X 1 1+(3014815199/5000000000 : ℝ)*X 1 2+(524332041/1000000000 : ℝ)*X 2 0+(-26667437/2000000000 : ℝ)*X 2 1+(3014815199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((198739/10000000000 : ℝ)*X 0 0+(-282032213/625000000 : ℝ)*X 0 1+(3382514873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2173578821/10000000000 : ℝ)*X 1 0+(1841749369/5000000000 : ℝ)*X 1 1+(152760183/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3955630653/5000000000 : ℝ)*X 2 0+(-168809427/1250000000 : ℝ)*X 2 1+(-2240249137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((713758859/1000000000 : ℝ)*X 0 0+(-369910817/2000000000 : ℝ)*X 0 1+(1386398413/5000000000 : ℝ)*X 0 2+(713758859/1000000000 : ℝ)*X 1 0+(-369910817/2000000000 : ℝ)*X 1 1+(1386398413/5000000000 : ℝ)*X 1 2+(713758859/1000000000 : ℝ)*X 2 0+(-369910817/2000000000 : ℝ)*X 2 1+(1386398413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((14773/5000000000 : ℝ)*X 0 0+(-2171319859/2500000000 : ℝ)*X 0 1+(2200291433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1501140871/2000000000 : ℝ)*X 1 0+(281307017/1250000000 : ℝ)*X 1 1+(1910065653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2556187627/10000000000 : ℝ)*X 2 0+(-5401592203/10000000000 : ℝ)*X 2 1+(-2056315907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((93691801/125000000 : ℝ)*X 0 0+(-23554087/250000000 : ℝ)*X 0 1+(3104301801/10000000000 : ℝ)*X 0 2+(93691801/125000000 : ℝ)*X 1 0+(-23554087/250000000 : ℝ)*X 1 1+(3104301801/10000000000 : ℝ)*X 1 2+(93691801/125000000 : ℝ)*X 2 0+(-23554087/250000000 : ℝ)*X 2 1+(3104301801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((42299/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42299/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (167697482487081601377/15625000000000000000000000 : ℝ) := by norm_num
    linear_combination (406801648933/500000000000 : ℝ)*(base7) + (6850401/1000000000000 : ℝ)*(base43) + (196456430973/500000000000 : ℝ)*(base50) + (1902077852337/1000000000000 : ℝ)*(major_s0_0) + (118879437621/62500000000 : ℝ)*(major_s0_1) + (1902077852337/1000000000000 : ℝ)*(major_s0_2) + (7880223/250000000000 : ℝ)*(sp_s0_0) + (18668957/500000000000 : ℝ)*(sp_s0_6) + (2437384006641/1000000000000 : ℝ)*(sp_s0_7) + (2437381175843/1000000000000 : ℝ)*(sp_s0_8) + (609353076873/250000000000 : ℝ)*(sp_s0_9) + (867859229543/500000000000 : ℝ)*(sp_s0_13) + (4120209/100000000000 : ℝ)*(sp_s0_15) + (80501/25000000000 : ℝ)*(sp_s0_23) + (922152499133/1000000000000 : ℝ)*(f.failure) + (1218711188967/500000000000 : ℝ)*(f.sum) + (1692288717339/200000000000000000000000000 : ℝ)*base62 + (5806116819233189/10000000000000000000000000000 : ℝ)*base65 + (555754548876237/625000000000000000000000000 : ℝ)*base66 + (76041800398891/200000000000000000000000000 : ℝ)*base68 + (3824124328288639/10000000000000000000000000000 : ℝ)*base71 + (1416027126233189/10000000000000000000000000000 : ℝ)*base72 + (2844320504903/12500000000000000000000000 : ℝ)*base74 + (28513359758891/200000000000000000000000000 : ℝ)*base76 + (4481952688252981/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (6351/20000000000000000 : ℝ)*base86 + (6351/20000000000000000 : ℝ)*base88 + (6351/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28903/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-28903/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11080894188346827718881/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (617629064879/500000000000 : ℝ)*(base7) + (72703061399/500000000000 : ℝ)*(base40) + (5080113/500000000000 : ℝ)*(base53) + (1951787956243/1000000000000 : ℝ)*(major_s0_0) + (1595750271969/1000000000000 : ℝ)*(major_s0_1) + (1595740111743/1000000000000 : ℝ)*(major_s0_2) + (13931877/1000000000000 : ℝ)*(sp_s0_0) + (10360207/500000000000 : ℝ)*(sp_s0_1) + (1742849821581/1000000000000 : ℝ)*(sp_s0_14) + (348568606609/200000000000 : ℝ)*(sp_s0_15) + (348574782737/200000000000 : ℝ)*(sp_s0_16) + (178018842137/500000000000 : ℝ)*(sp_s0_17) + (20088727639/10000000000 : ℝ)*(sp_s0_20) + (2620263/100000000000 : ℝ)*(sp_s0_27) + (773640836773/1000000000000 : ℝ)*(f.failure) + (348574782737/200000000000 : ℝ)*(f.sum) + (666879260687/6250000000000000000000000 : ℝ)*base63 + (4039696466757429/10000000000000000000000000000 : ℝ)*base64 + (4871000111278507/10000000000000000000000000000 : ℝ)*base67 + (29138830547451/200000000000000000000000000 : ℝ)*base69 + (2831404184059879/10000000000000000000000000000 : ℝ)*base70 + (221028971590929/10000000000000000000000000000 : ℝ)*base73 + (26891539545467/200000000000000000000000000 : ℝ)*base74 + (37707345346049/200000000000000000000000000 : ℝ)*base76 + (849480396217359/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (16569/20000000000000000 : ℝ)*base87 + (16569/20000000000000000 : ℝ)*base89 + (16569/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32553/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32553/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23112333243791166030663/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1237636694377/1000000000000 : ℝ)*(base7) + (124470993573/1000000000000 : ℝ)*(base40) + (527123777/1953125000 : ℝ)*(base43) + (54906253697/500000000000 : ℝ)*(base50) + (1590282763927/1000000000000 : ℝ)*(major_s0_0) + (1320395390103/1000000000000 : ℝ)*(major_s0_1) + (1590282763927/1000000000000 : ℝ)*(major_s0_2) + (10671907/1000000000000 : ℝ)*(sp_s0_2) + (48056713/1000000000000 : ℝ)*(sp_s0_7) + (891787/500000000000 : ℝ)*(sp_s0_20) + (182919577627/125000000000 : ℝ)*(sp_s0_21) + (54165376611/31250000000 : ℝ)*(sp_s0_22) + (1463394005821/1000000000000 : ℝ)*(sp_s0_23) + (1004312513683/500000000000 : ℝ)*(sp_s0_27) + (385495058281/500000000000 : ℝ)*(f.failure) + (54165376611/31250000000 : ℝ)*(f.sum) + (6743104793929/20000000000000000000000000 : ℝ)*base62 + (9333210874612419/10000000000000000000000000000 : ℝ)*base65 + (5663898456063491/10000000000000000000000000000 : ℝ)*base66 + (87440206465261/200000000000000000000000000 : ℝ)*base68 + (5560562993349369/10000000000000000000000000000 : ℝ)*base71 + (6241845764612419/10000000000000000000000000000 : ℝ)*base72 + (32371238514029/200000000000000000000000000 : ℝ)*base74 + (141841640934739/200000000000000000000000000 : ℝ)*base77 + (1080764777467591/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (3907/10000000000000000 : ℝ)*base86 + (3907/10000000000000000 : ℝ)*base88 + (3907/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (42299/100000 : ℝ) ^ (87/16 : ℝ) ≤ (464664960524351359/50000000000000000000 : ℝ) := by
    have hpowers : (42299/100000 : ℝ)^87 ≤ (464664960524351359/50000000000000000000 : ℝ)^16 := by
      have hnat : (42299 : ℕ)^87*50000000000000000000^16 ≤ 464664960524351359^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42299 100000 464664960524351359 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42299/100000 : ℝ)) (X := (464664960524351359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50464664960524351359/50000000000000000000 : ℝ) ≤ (100170266760909/100000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50464664960524351359/50000000000000000000 : ℝ)^16 ≤ (100170266760909/100000000000000 : ℝ)^87 := by
      have hnat : (50464664960524351359 : ℕ)^16*100000000000000^87 ≤ 100170266760909^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50464664960524351359 50000000000000000000 100170266760909 100000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100170266760909/100000000000000 : ℝ)) (X := (50464664960524351359/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25464664960524351359/25000000000000000000 : ℝ) ≤ (5016962942349461/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25464664960524351359/25000000000000000000 : ℝ)^16 ≤ (5016962942349461/5000000000000000 : ℝ)^87 := by
      have hnat : (25464664960524351359 : ℕ)^16*5000000000000000^87 ≤ 5016962942349461^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25464664960524351359 25000000000000000000 5016962942349461 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016962942349461/5000000000000000 : ℝ)) (X := (25464664960524351359/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(170266760909/42299000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8449604304011/2114950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (42299/100000 : ℝ)) (alpha := (170266760909/42299000000000 : ℝ)) (beta := (8449604304011/2114950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42299/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(170266760909/42299000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8449604304011/2114950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (28903/50000 : ℝ) ^ (87/16 : ℝ) ≤ (2539204908662032487/50000000000000000000 : ℝ) := by
    have hpowers : (28903/50000 : ℝ)^87 ≤ (2539204908662032487/50000000000000000000 : ℝ)^16 := by
      have hnat : (28903 : ℕ)^87*50000000000000000000^16 ≤ 2539204908662032487^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28903 50000 2539204908662032487 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28903/50000 : ℝ)) (X := (2539204908662032487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (52539204908662032487/50000000000000000000 : ℝ) ≤ (10091518117703483/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (52539204908662032487/50000000000000000000 : ℝ)^16 ≤ (10091518117703483/10000000000000000 : ℝ)^87 := by
      have hnat : (52539204908662032487 : ℕ)^16*10000000000000000^87 ≤ 10091518117703483^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52539204908662032487 50000000000000000000 10091518117703483 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091518117703483/10000000000000000 : ℝ)) (X := (52539204908662032487/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (27539204908662032487/25000000000000000000 : ℝ) ≤ (2035898995477869/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (27539204908662032487/25000000000000000000 : ℝ)^16 ≤ (2035898995477869/2000000000000000 : ℝ)^87 := by
      have hnat : (27539204908662032487 : ℕ)^16*2000000000000000^87 ≤ 2035898995477869^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27539204908662032487 25000000000000000000 2035898995477869 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2035898995477869/2000000000000000 : ℝ)) (X := (27539204908662032487/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(91518117703483/5780600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6284061406133/412900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (28903/50000 : ℝ)) (alpha := (91518117703483/5780600000000000 : ℝ)) (beta := (6284061406133/412900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (28903/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(91518117703483/5780600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6284061406133/412900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (32553/50000 : ℝ) ^ (87/16 : ℝ) ≤ (9695367217855334139/100000000000000000000 : ℝ) := by
    have hpowers : (32553/50000 : ℝ)^87 ≤ (9695367217855334139/100000000000000000000 : ℝ)^16 := by
      have hnat : (32553 : ℕ)^87*100000000000000000000^16 ≤ 9695367217855334139^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32553 50000 9695367217855334139 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32553/50000 : ℝ)) (X := (9695367217855334139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (109695367217855334139/100000000000000000000 : ℝ) ≤ (5085819627749533/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (109695367217855334139/100000000000000000000 : ℝ)^16 ≤ (5085819627749533/5000000000000000 : ℝ)^87 := by
      have hnat : (109695367217855334139 : ℕ)^16*5000000000000000^87 ≤ 5085819627749533^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109695367217855334139 100000000000000000000 5085819627749533 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5085819627749533/5000000000000000 : ℝ)) (X := (109695367217855334139/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59695367217855334139/50000000000000000000 : ℝ) ≤ (10331312947202373/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (59695367217855334139/50000000000000000000 : ℝ)^16 ≤ (10331312947202373/10000000000000000 : ℝ)^87 := by
      have hnat : (59695367217855334139 : ℕ)^16*10000000000000000^87 ≤ 10331312947202373^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59695367217855334139 50000000000000000000 10331312947202373 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10331312947202373/10000000000000000 : ℝ)) (X := (59695367217855334139/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(85819627749533/3255300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(159673691703307/6510600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (32553/50000 : ℝ)) (alpha := (85819627749533/3255300000000000 : ℝ)) (beta := (159673691703307/6510600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32553/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(85819627749533/3255300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(159673691703307/6510600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-904293779/10000000000 : ℝ)*X 0 0+(-1368569503/2500000000 : ℝ)*X 0 1+(5354074951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5379387301/10000000000 : ℝ)*X 1 0+(667699221/2000000000 : ℝ)*X 1 1+(678987727/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((167526419/312500000 : ℝ)*X 2 0+(-133942623/400000000 : ℝ)*X 2 1+(-425675201/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1021728031/2000000000 : ℝ)*X 0 0+(-700892439/2000000000 : ℝ)*X 0 1+(705191209/2000000000 : ℝ)*X 0 2+(1021728031/2000000000 : ℝ)*X 1 0+(-700892439/2000000000 : ℝ)*X 1 1+(705191209/2000000000 : ℝ)*X 1 2+(1021728031/2000000000 : ℝ)*X 2 0+(-700892439/2000000000 : ℝ)*X 2 1+(705191209/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326045_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-51472055328373723644026528999375761/5527535556436250000000000000000000 : ℝ) := by norm_num
    linear_combination (7437/1000000000000 : ℝ)*(base7) + (50881/1000000000000 : ℝ)*(base17) + (1613/50000000000 : ℝ)*(base19) + (129/7812500000 : ℝ)*(base22) + (729/125000000000 : ℝ)*(base39) + (664513383887/1000000000000 : ℝ)*(base40) + (79553168487/1000000000000 : ℝ)*(base50) + (2543460397/40000000000 : ℝ)*(base60) + (41253/20000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (387997317667/125000000000 : ℝ)*(sp_s1_0) + (620795691639/200000000000 : ℝ)*(sp_s1_1) + (387997315603/125000000000 : ℝ)*(sp_s1_2) + (1000000007437/1000000000000 : ℝ)*(sp_s1_6) + (387997317667/125000000000 : ℝ)*(f.sum) + (1022364843845286077/3136264530000000000000000000000 : ℝ)*base63 + (11779965771803/108510000000000000000000000 : ℝ)*base64 + (6945750578929/41290000000000000000000000 : ℝ)*base66 + (667976077993/10851000000000000000000000 : ℝ)*base68 + (39889589926559537/229493224500000000000000000000 : ℝ)*base70 + (6584234875651/42299000000000000000000000 : ℝ)*base72 + (178696700986919/289030000000000000000000000 : ℝ)*base75 + (3154353071297/84598000000000000000000000 : ℝ)*base77 + (882452828687499283/1746525710000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c326046_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-218906277/2500000000 : ℝ)*x 0 + (-108477943/200000000 : ℝ)*x 1 + (-108477943/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218906277/2500000000 : ℝ)^89 ≤ (641811585029/12500000000000 : ℝ)^73 := by
    have hnat : (218906277 : ℕ)^89*12500000000000^73 ≤ 641811585029^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218906277 2500000000 641811585029 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108477943/200000000 : ℝ)^89 ≤ (11858188414403/25000000000000 : ℝ)^73 := by
    have hnat : (108477943 : ℕ)^89*25000000000000^73 ≤ 11858188414403^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108477943 200000000 11858188414403 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108477943/200000000 : ℝ)^89 ≤ (11858188414403/25000000000000 : ℝ)^73 := by
    have hnat : (108477943 : ℕ)^89*25000000000000^73 ≤ 11858188414403^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108477943 200000000 11858188414403 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218906277/2500000000 : ℝ), (-108477943/200000000 : ℝ), (-108477943/200000000 : ℝ)] ![(641811585029/12500000000000 : ℝ), (11858188414403/25000000000000 : ℝ), (11858188414403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218906277/2500000000 : ℝ)|^89 ≤ (641811585029/12500000000000 : ℝ)^73
        have hw : |(-218906277/2500000000 : ℝ)|=(218906277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108477943/200000000 : ℝ)|^89 ≤ (11858188414403/25000000000000 : ℝ)^73
        have hw : |(-108477943/200000000 : ℝ)|=(108477943/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108477943/200000000 : ℝ)|^89 ≤ (11858188414403/25000000000000 : ℝ)^73
        have hw : |(-108477943/200000000 : ℝ)|=(108477943/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326046_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1209640723/2500000000 : ℝ)*x 0 + (3660271599/10000000000 : ℝ)*x 1 + (-3660271599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1209640723/2500000000 : ℝ)^89 ≤ (20633986300037/50000000000000 : ℝ)^73 := by
    have hnat : (1209640723 : ℕ)^89*50000000000000^73 ≤ 20633986300037^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209640723 2500000000 20633986300037 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660271599/10000000000 : ℝ)^89 ≤ (14683006843987/50000000000000 : ℝ)^73 := by
    have hnat : (3660271599 : ℕ)^89*50000000000000^73 ≤ 14683006843987^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660271599 10000000000 14683006843987 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3660271599/10000000000 : ℝ)^89 ≤ (14683006843987/50000000000000 : ℝ)^73 := by
    have hnat : (3660271599 : ℕ)^89*50000000000000^73 ≤ 14683006843987^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660271599 10000000000 14683006843987 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1209640723/2500000000 : ℝ), (3660271599/10000000000 : ℝ), (-3660271599/10000000000 : ℝ)] ![(20633986300037/50000000000000 : ℝ), (14683006843987/50000000000000 : ℝ), (14683006843987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1209640723/2500000000 : ℝ)|^89 ≤ (20633986300037/50000000000000 : ℝ)^73
        have hw : |(1209640723/2500000000 : ℝ)|=(1209640723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3660271599/10000000000 : ℝ)|^89 ≤ (14683006843987/50000000000000 : ℝ)^73
        have hw : |(3660271599/10000000000 : ℝ)|=(3660271599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3660271599/10000000000 : ℝ)|^89 ≤ (14683006843987/50000000000000 : ℝ)^73
        have hw : |(-3660271599/10000000000 : ℝ)|=(3660271599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326046_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1209640723/2500000000 : ℝ)*x 0 + (-3660271599/10000000000 : ℝ)*x 1 + (3660271599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1209640723/2500000000 : ℝ)^89 ≤ (20633986300037/50000000000000 : ℝ)^73 := by
    have hnat : (1209640723 : ℕ)^89*50000000000000^73 ≤ 20633986300037^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209640723 2500000000 20633986300037 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660271599/10000000000 : ℝ)^89 ≤ (14683006843987/50000000000000 : ℝ)^73 := by
    have hnat : (3660271599 : ℕ)^89*50000000000000^73 ≤ 14683006843987^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660271599 10000000000 14683006843987 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3660271599/10000000000 : ℝ)^89 ≤ (14683006843987/50000000000000 : ℝ)^73 := by
    have hnat : (3660271599 : ℕ)^89*50000000000000^73 ≤ 14683006843987^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660271599 10000000000 14683006843987 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1209640723/2500000000 : ℝ), (-3660271599/10000000000 : ℝ), (3660271599/10000000000 : ℝ)] ![(20633986300037/50000000000000 : ℝ), (14683006843987/50000000000000 : ℝ), (14683006843987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1209640723/2500000000 : ℝ)|^89 ≤ (20633986300037/50000000000000 : ℝ)^73
        have hw : |(1209640723/2500000000 : ℝ)|=(1209640723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3660271599/10000000000 : ℝ)|^89 ≤ (14683006843987/50000000000000 : ℝ)^73
        have hw : |(-3660271599/10000000000 : ℝ)|=(3660271599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3660271599/10000000000 : ℝ)|^89 ≤ (14683006843987/50000000000000 : ℝ)^73
        have hw : |(3660271599/10000000000 : ℝ)|=(3660271599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326046_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8339646863/10000000000 : ℝ)*x 0 + (-300781607/2000000000 : ℝ)*x 1 + (-300781607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8339646863/10000000000 : ℝ)^89 ≤ (20035720534491/25000000000000 : ℝ)^73 := by
    have hnat : (8339646863 : ℕ)^89*25000000000000^73 ≤ 20035720534491^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8339646863 10000000000 20035720534491 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300781607/2000000000 : ℝ)^89 ≤ (9928558925627/100000000000000 : ℝ)^73 := by
    have hnat : (300781607 : ℕ)^89*100000000000000^73 ≤ 9928558925627^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300781607 2000000000 9928558925627 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300781607/2000000000 : ℝ)^89 ≤ (9928558925627/100000000000000 : ℝ)^73 := by
    have hnat : (300781607 : ℕ)^89*100000000000000^73 ≤ 9928558925627^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300781607 2000000000 9928558925627 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8339646863/10000000000 : ℝ), (-300781607/2000000000 : ℝ), (-300781607/2000000000 : ℝ)] ![(20035720534491/25000000000000 : ℝ), (9928558925627/100000000000000 : ℝ), (9928558925627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8339646863/10000000000 : ℝ)|^89 ≤ (20035720534491/25000000000000 : ℝ)^73
        have hw : |(8339646863/10000000000 : ℝ)|=(8339646863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300781607/2000000000 : ℝ)|^89 ≤ (9928558925627/100000000000000 : ℝ)^73
        have hw : |(-300781607/2000000000 : ℝ)|=(300781607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300781607/2000000000 : ℝ)|^89 ≤ (9928558925627/100000000000000 : ℝ)^73
        have hw : |(-300781607/2000000000 : ℝ)|=(300781607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326046 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-218906277/2500000000 : ℝ)*X 0 0+(-108477943/200000000 : ℝ)*X 0 1+(-108477943/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1209640723/2500000000 : ℝ)*X 1 0+(3660271599/10000000000 : ℝ)*X 1 1+(-3660271599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1209640723/2500000000 : ℝ)*X 2 0+(-3660271599/10000000000 : ℝ)*X 2 1+(3660271599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((8339646863/10000000000 : ℝ)*X 0 0+(-300781607/2000000000 : ℝ)*X 0 1+(-300781607/2000000000 : ℝ)*X 0 2+(8339646863/10000000000 : ℝ)*X 1 0+(-300781607/2000000000 : ℝ)*X 1 1+(-300781607/2000000000 : ℝ)*X 1 2+(8339646863/10000000000 : ℝ)*X 2 0+(-300781607/2000000000 : ℝ)*X 2 1+(-300781607/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326046_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-4678403795445368482726285587/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2679/1000000000000 : ℝ)*(base18) + (134932208407/125000000000 : ℝ)*(base39) + (245106273709/500000000000 : ℝ)*(base40) + (229/1000000000000 : ℝ)*(base43) + (391816251/10000000000 : ℝ)*(base49) + (9795405739/250000000000 : ℝ)*(base59) + (41253/20000 : ℝ)*(major_s0_0) + (2062649999771/1000000000000 : ℝ)*(major_s0_1) + (2062650001741/1000000000000 : ℝ)*(major_s0_2) + (3118935857391/1000000000000 : ℝ)*(sp_s0_0) + (3118935856203/1000000000000 : ℝ)*(sp_s0_1) + (3118935855649/1000000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (3118935855879/1000000000000 : ℝ)*(f.sum) + (168224607073/25000000000000000000000000 : ℝ)*base63 + (3153913229723377/10000000000000000000000000000 : ℝ)*base64 + (4338295991732713/10000000000000000000000000000 : ℝ)*base67 + (11828053683937/200000000000000000000000000 : ℝ)*base69 + (12625927824976723377/10000000000000000000000000000 : ℝ)*base70 + (2468876547/10000000000000000000000 : ℝ)*base73 + (56102358932647/200000000000000000000000000 : ℝ)*base75 + (9535284749/10000000000000000000000 : ℝ)*base76 + (3568545540732713/10000000000000000000000000000 : ℝ)*base79 + (1741/1000000000000 : ℝ)*base81 + (3003/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (1741/1000000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b021 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 45 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=45 ∨ c=46 := by omega
  rcases hc with rfl|rfl
  · exact collision_c326045 p hpa (by linarith only [hpb]) X hX
  · exact collision_c326046 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 45 ≤ c.val) (hhi : c.val < 47)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
