-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b043
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:00.090914+00:00
-- url     : https://prove2.me/submissions/2b4af5a8-5b7a-44ee-bf01-29cb0a9bd3fd

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
theorem collision_support_c325085_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-511173177/2500000000 : ℝ)*x 0 + (-214770731/312500000 : ℝ)*x 1 + (2965037923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511173177/2500000000 : ℝ)^87 ≤ (714902188793/5000000000000 : ℝ)^71 := by
    have hnat : (511173177 : ℕ)^87*5000000000000^71 ≤ 714902188793^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511173177 2500000000 714902188793 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214770731/312500000 : ℝ)^87 ≤ (63156908722081/100000000000000 : ℝ)^71 := by
    have hnat : (214770731 : ℕ)^87*100000000000000^71 ≤ 63156908722081^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214770731 312500000 63156908722081 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2965037923/10000000000 : ℝ)^87 ≤ (22545047483239/100000000000000 : ℝ)^71 := by
    have hnat : (2965037923 : ℕ)^87*100000000000000^71 ≤ 22545047483239^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965037923 10000000000 22545047483239 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511173177/2500000000 : ℝ), (-214770731/312500000 : ℝ), (2965037923/10000000000 : ℝ)] ![(714902188793/5000000000000 : ℝ), (63156908722081/100000000000000 : ℝ), (22545047483239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511173177/2500000000 : ℝ)|^87 ≤ (714902188793/5000000000000 : ℝ)^71
        have hw : |(-511173177/2500000000 : ℝ)|=(511173177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214770731/312500000 : ℝ)|^87 ≤ (63156908722081/100000000000000 : ℝ)^71
        have hw : |(-214770731/312500000 : ℝ)|=(214770731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2965037923/10000000000 : ℝ)|^87 ≤ (22545047483239/100000000000000 : ℝ)^71
        have hw : |(2965037923/10000000000 : ℝ)|=(2965037923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325085_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5515411857/10000000000 : ℝ)*x 0 + (520306067/2000000000 : ℝ)*x 1 + (1000583323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515411857/10000000000 : ℝ)^87 ≤ (48232746571037/100000000000000 : ℝ)^71 := by
    have hnat : (5515411857 : ℕ)^87*100000000000000^71 ≤ 48232746571037^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515411857 10000000000 48232746571037 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520306067/2000000000 : ℝ)^87 ≤ (9603277853439/50000000000000 : ℝ)^71 := by
    have hnat : (520306067 : ℕ)^87*50000000000000^71 ≤ 9603277853439^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520306067 2000000000 9603277853439 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000583323/2500000000 : ℝ)^87 ≤ (6512139543269/20000000000000 : ℝ)^71 := by
    have hnat : (1000583323 : ℕ)^87*20000000000000^71 ≤ 6512139543269^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000583323 2500000000 6512139543269 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515411857/10000000000 : ℝ), (520306067/2000000000 : ℝ), (1000583323/2500000000 : ℝ)] ![(48232746571037/100000000000000 : ℝ), (9603277853439/50000000000000 : ℝ), (6512139543269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515411857/10000000000 : ℝ)|^87 ≤ (48232746571037/100000000000000 : ℝ)^71
        have hw : |(5515411857/10000000000 : ℝ)|=(5515411857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520306067/2000000000 : ℝ)|^87 ≤ (9603277853439/50000000000000 : ℝ)^71
        have hw : |(520306067/2000000000 : ℝ)|=(520306067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000583323/2500000000 : ℝ)|^87 ≤ (6512139543269/20000000000000 : ℝ)^71
        have hw : |(1000583323/2500000000 : ℝ)|=(1000583323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325085_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (185829483/500000000 : ℝ)*x 0 + (-398807023/1250000000 : ℝ)*x 1 + (-5268606139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185829483/500000000 : ℝ)^87 ≤ (5947107524229/20000000000000 : ℝ)^71 := by
    have hnat : (185829483 : ℕ)^87*20000000000000^71 ≤ 5947107524229^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185829483 500000000 5947107524229 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398807023/1250000000 : ℝ)^87 ≤ (24662946535121/100000000000000 : ℝ)^71 := by
    have hnat : (398807023 : ℕ)^87*100000000000000^71 ≤ 24662946535121^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398807023 1250000000 24662946535121 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5268606139/10000000000 : ℝ)^87 ≤ (45601515828123/100000000000000 : ℝ)^71 := by
    have hnat : (5268606139 : ℕ)^87*100000000000000^71 ≤ 45601515828123^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268606139 10000000000 45601515828123 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(185829483/500000000 : ℝ), (-398807023/1250000000 : ℝ), (-5268606139/10000000000 : ℝ)] ![(5947107524229/20000000000000 : ℝ), (24662946535121/100000000000000 : ℝ), (45601515828123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(185829483/500000000 : ℝ)|^87 ≤ (5947107524229/20000000000000 : ℝ)^71
        have hw : |(185829483/500000000 : ℝ)|=(185829483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398807023/1250000000 : ℝ)|^87 ≤ (24662946535121/100000000000000 : ℝ)^71
        have hw : |(-398807023/1250000000 : ℝ)|=(398807023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5268606139/10000000000 : ℝ)|^87 ≤ (45601515828123/100000000000000 : ℝ)^71
        have hw : |(-5268606139/10000000000 : ℝ)|=(5268606139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325085_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6769063141/10000000000 : ℝ)*x 0 + (-974435083/5000000000 : ℝ)*x 1 + (317602509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6769063141/10000000000 : ℝ)^87 ≤ (30996154975119/50000000000000 : ℝ)^71 := by
    have hnat : (6769063141 : ℕ)^87*50000000000000^71 ≤ 30996154975119^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6769063141 10000000000 30996154975119 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974435083/5000000000 : ℝ)^87 ≤ (13481368660089/100000000000000 : ℝ)^71 := by
    have hnat : (974435083 : ℕ)^87*100000000000000^71 ≤ 13481368660089^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974435083 5000000000 13481368660089 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317602509/1000000000 : ℝ)^87 ≤ (981052855057/4000000000000 : ℝ)^71 := by
    have hnat : (317602509 : ℕ)^87*4000000000000^71 ≤ 981052855057^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317602509 1000000000 981052855057 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6769063141/10000000000 : ℝ), (-974435083/5000000000 : ℝ), (317602509/1000000000 : ℝ)] ![(30996154975119/50000000000000 : ℝ), (13481368660089/100000000000000 : ℝ), (981052855057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6769063141/10000000000 : ℝ)|^87 ≤ (30996154975119/50000000000000 : ℝ)^71
        have hw : |(6769063141/10000000000 : ℝ)|=(6769063141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974435083/5000000000 : ℝ)|^87 ≤ (13481368660089/100000000000000 : ℝ)^71
        have hw : |(-974435083/5000000000 : ℝ)|=(974435083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317602509/1000000000 : ℝ)|^87 ≤ (981052855057/4000000000000 : ℝ)^71
        have hw : |(317602509/1000000000 : ℝ)|=(317602509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325085 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-511173177/2500000000 : ℝ)*X 0 0+(-214770731/312500000 : ℝ)*X 0 1+(2965037923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5515411857/10000000000 : ℝ)*X 1 0+(520306067/2000000000 : ℝ)*X 1 1+(1000583323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((185829483/500000000 : ℝ)*X 2 0+(-398807023/1250000000 : ℝ)*X 2 1+(-5268606139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6769063141/10000000000 : ℝ)*X 0 0+(-974435083/5000000000 : ℝ)*X 0 1+(317602509/1000000000 : ℝ)*X 0 2+(6769063141/10000000000 : ℝ)*X 1 0+(-974435083/5000000000 : ℝ)*X 1 1+(317602509/1000000000 : ℝ)*X 1 2+(6769063141/10000000000 : ℝ)*X 2 0+(-974435083/5000000000 : ℝ)*X 2 1+(317602509/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-11256237650513309982171/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (343079758057/1000000000000 : ℝ)*(base3) + (32787/200000000000 : ℝ)*(base10) + (36731/1000000000000 : ℝ)*(base19) + (23239/500000000000 : ℝ)*(base21) + (23749/125000000000 : ℝ)*(base24) + (49863/1000000000000 : ℝ)*(base27) + (10057035371/15625000000 : ℝ)*(base40) + (157674731461/250000000000 : ℝ)*(base50) + (200939/100000 : ℝ)*(major_s0_0) + (200939/100000 : ℝ)*(major_s0_1) + (200939/100000 : ℝ)*(major_s0_2) + (3001663209531/1000000000000 : ℝ)*(sp_s0_0) + (3344743094793/1000000000000 : ℝ)*(sp_s0_1) + (3001663136997/1000000000000 : ℝ)*(sp_s0_2) + (8211502401/12500000000 : ℝ)*(sp_s0_6) + (1500831686733/500000000000 : ℝ)*(f.sum) + (410707269/1250000000000000000000 : ℝ)*base62 + (2013009329/5000000000000000000000 : ℝ)*base64 + (2523303403/10000000000000000000000 : ℝ)*base66 + (2041311791/10000000000000000000000 : ℝ)*base68 + (9690251/80000000000000000000 : ℝ)*base70 + (1089171333/5000000000000000000000 : ℝ)*base72 + (492508121/1000000000000000000000 : ℝ)*base74 + (66648409/5000000000000000000000 : ℝ)*base77 + (1835658383/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c325086_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (310241533/500000000 : ℝ)*x 0 + (1493521889/5000000000 : ℝ)*x 1 + (57109347/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (310241533/500000000 : ℝ)^87 ≤ (2228851722097/4000000000000 : ℝ)^71 := by
    have hnat : (310241533 : ℕ)^87*4000000000000^71 ≤ 2228851722097^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310241533 500000000 2228851722097 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493521889/5000000000 : ℝ)^87 ≤ (1137512493069/5000000000000 : ℝ)^71 := by
    have hnat : (1493521889 : ℕ)^87*5000000000000^71 ≤ 1137512493069^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493521889 5000000000 1137512493069 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57109347/200000000 : ℝ)^87 ≤ (21528457076139/100000000000000 : ℝ)^71 := by
    have hnat : (57109347 : ℕ)^87*100000000000000^71 ≤ 21528457076139^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57109347 200000000 21528457076139 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(310241533/500000000 : ℝ), (1493521889/5000000000 : ℝ), (57109347/200000000 : ℝ)] ![(2228851722097/4000000000000 : ℝ), (1137512493069/5000000000000 : ℝ), (21528457076139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(310241533/500000000 : ℝ)|^87 ≤ (2228851722097/4000000000000 : ℝ)^71
        have hw : |(310241533/500000000 : ℝ)|=(310241533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1493521889/5000000000 : ℝ)|^87 ≤ (1137512493069/5000000000000 : ℝ)^71
        have hw : |(1493521889/5000000000 : ℝ)|=(1493521889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57109347/200000000 : ℝ)|^87 ≤ (21528457076139/100000000000000 : ℝ)^71
        have hw : |(57109347/200000000 : ℝ)|=(57109347/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2935279501/5000000000 : ℝ)*x 0 + (-3217788899/10000000000 : ℝ)*x 1 + (-188443319/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2935279501/5000000000 : ℝ)^87 ≤ (26032800404219/50000000000000 : ℝ)^71 := by
    have hnat : (2935279501 : ℕ)^87*50000000000000^71 ≤ 26032800404219^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935279501 5000000000 26032800404219 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3217788899/10000000000 : ℝ)^87 ≤ (24922098169601/100000000000000 : ℝ)^71 := by
    have hnat : (3217788899 : ℕ)^87*100000000000000^71 ≤ 24922098169601^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3217788899 10000000000 24922098169601 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188443319/625000000 : ℝ)^87 ≤ (23012301016039/100000000000000 : ℝ)^71 := by
    have hnat : (188443319 : ℕ)^87*100000000000000^71 ≤ 23012301016039^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188443319 625000000 23012301016039 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2935279501/5000000000 : ℝ), (-3217788899/10000000000 : ℝ), (-188443319/625000000 : ℝ)] ![(26032800404219/50000000000000 : ℝ), (24922098169601/100000000000000 : ℝ), (23012301016039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2935279501/5000000000 : ℝ)|^87 ≤ (26032800404219/50000000000000 : ℝ)^71
        have hw : |(2935279501/5000000000 : ℝ)|=(2935279501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3217788899/10000000000 : ℝ)|^87 ≤ (24922098169601/100000000000000 : ℝ)^71
        have hw : |(-3217788899/10000000000 : ℝ)|=(3217788899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188443319/625000000 : ℝ)|^87 ≤ (23012301016039/100000000000000 : ℝ)^71
        have hw : |(-188443319/625000000 : ℝ)|=(188443319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3448807073/10000000000 : ℝ)*x 0 + (-2141287409/10000000000 : ℝ)*x 1 + (255499723/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3448807073/10000000000 : ℝ)^87 ≤ (27131987636763/100000000000000 : ℝ)^71 := by
    have hnat : (3448807073 : ℕ)^87*100000000000000^71 ≤ 27131987636763^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448807073 10000000000 27131987636763 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141287409/10000000000 : ℝ)^87 ≤ (7565038743557/50000000000000 : ℝ)^71 := by
    have hnat : (2141287409 : ℕ)^87*50000000000000^71 ≤ 7565038743557^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141287409 10000000000 7565038743557 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255499723/400000000 : ℝ)^87 ≤ (11547586971877/20000000000000 : ℝ)^71 := by
    have hnat : (255499723 : ℕ)^87*20000000000000^71 ≤ 11547586971877^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255499723 400000000 11547586971877 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3448807073/10000000000 : ℝ), (-2141287409/10000000000 : ℝ), (255499723/400000000 : ℝ)] ![(27131987636763/100000000000000 : ℝ), (7565038743557/50000000000000 : ℝ), (11547586971877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3448807073/10000000000 : ℝ)|^87 ≤ (27131987636763/100000000000000 : ℝ)^71
        have hw : |(3448807073/10000000000 : ℝ)|=(3448807073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141287409/10000000000 : ℝ)|^87 ≤ (7565038743557/50000000000000 : ℝ)^71
        have hw : |(-2141287409/10000000000 : ℝ)|=(2141287409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255499723/400000000 : ℝ)|^87 ≤ (11547586971877/20000000000000 : ℝ)^71
        have hw : |(255499723/400000000 : ℝ)|=(255499723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-206353/10000000000 : ℝ)*x 0 + (-4218159589/5000000000 : ℝ)*x 1 + (127870341/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206353/10000000000 : ℝ)^87 ≤ (181446431/100000000000000 : ℝ)^71 := by
    have hnat : (206353 : ℕ)^87*100000000000000^71 ≤ 181446431^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206353 10000000000 181446431 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218159589/5000000000 : ℝ)^87 ≤ (81191660863607/100000000000000 : ℝ)^71 := by
    have hnat : (4218159589 : ℕ)^87*100000000000000^71 ≤ 81191660863607^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218159589 5000000000 81191660863607 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127870341/500000000 : ℝ)^87 ≤ (587754927509/3125000000000 : ℝ)^71 := by
    have hnat : (127870341 : ℕ)^87*3125000000000^71 ≤ 587754927509^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127870341 500000000 587754927509 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206353/10000000000 : ℝ), (-4218159589/5000000000 : ℝ), (127870341/500000000 : ℝ)] ![(181446431/100000000000000 : ℝ), (81191660863607/100000000000000 : ℝ), (587754927509/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206353/10000000000 : ℝ)|^87 ≤ (181446431/100000000000000 : ℝ)^71
        have hw : |(-206353/10000000000 : ℝ)|=(206353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4218159589/5000000000 : ℝ)|^87 ≤ (81191660863607/100000000000000 : ℝ)^71
        have hw : |(-4218159589/5000000000 : ℝ)|=(4218159589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127870341/500000000 : ℝ)|^87 ≤ (587754927509/3125000000000 : ℝ)^71
        have hw : |(127870341/500000000 : ℝ)|=(127870341/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (966238999/2000000000 : ℝ)*x 0 + (508263103/1000000000 : ℝ)*x 1 + (216736981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966238999/2000000000 : ℝ)^87 ≤ (4100677315759/10000000000000 : ℝ)^71 := by
    have hnat : (966238999 : ℕ)^87*10000000000000^71 ≤ 4100677315759^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966238999 2000000000 4100677315759 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508263103/1000000000 : ℝ)^87 ≤ (8727402798851/20000000000000 : ℝ)^71 := by
    have hnat : (508263103 : ℕ)^87*20000000000000^71 ≤ 8727402798851^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508263103 1000000000 8727402798851 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216736981/1000000000 : ℝ)^87 ≤ (3071242566393/20000000000000 : ℝ)^71 := by
    have hnat : (216736981 : ℕ)^87*20000000000000^71 ≤ 3071242566393^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216736981 1000000000 3071242566393 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(966238999/2000000000 : ℝ), (508263103/1000000000 : ℝ), (216736981/1000000000 : ℝ)] ![(4100677315759/10000000000000 : ℝ), (8727402798851/20000000000000 : ℝ), (3071242566393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(966238999/2000000000 : ℝ)|^87 ≤ (4100677315759/10000000000000 : ℝ)^71
        have hw : |(966238999/2000000000 : ℝ)|=(966238999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508263103/1000000000 : ℝ)|^87 ≤ (8727402798851/20000000000000 : ℝ)^71
        have hw : |(508263103/1000000000 : ℝ)|=(508263103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216736981/1000000000 : ℝ)|^87 ≤ (3071242566393/20000000000000 : ℝ)^71
        have hw : |(216736981/1000000000 : ℝ)|=(216736981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5792534981/10000000000 : ℝ)*x 0 + (-2866242799/10000000000 : ℝ)*x 1 + (-3450987577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5792534981/10000000000 : ℝ)^87 ≤ (12804735931147/25000000000000 : ℝ)^71 := by
    have hnat : (5792534981 : ℕ)^87*25000000000000^71 ≤ 12804735931147^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5792534981 10000000000 12804735931147 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2866242799/10000000000 : ℝ)^87 ≤ (2703505904461/12500000000000 : ℝ)^71 := by
    have hnat : (2866242799 : ℕ)^87*12500000000000^71 ≤ 2703505904461^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2866242799 10000000000 2703505904461 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3450987577/10000000000 : ℝ)^87 ≤ (27153009026991/100000000000000 : ℝ)^71 := by
    have hnat : (3450987577 : ℕ)^87*100000000000000^71 ≤ 27153009026991^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3450987577 10000000000 27153009026991 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5792534981/10000000000 : ℝ), (-2866242799/10000000000 : ℝ), (-3450987577/10000000000 : ℝ)] ![(12804735931147/25000000000000 : ℝ), (2703505904461/12500000000000 : ℝ), (27153009026991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5792534981/10000000000 : ℝ)|^87 ≤ (12804735931147/25000000000000 : ℝ)^71
        have hw : |(5792534981/10000000000 : ℝ)|=(5792534981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2866242799/10000000000 : ℝ)|^87 ≤ (2703505904461/12500000000000 : ℝ)^71
        have hw : |(-2866242799/10000000000 : ℝ)|=(2866242799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3450987577/10000000000 : ℝ)|^87 ≤ (27153009026991/100000000000000 : ℝ)^71
        have hw : |(-3450987577/10000000000 : ℝ)|=(3450987577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2781687547/10000000000 : ℝ)*x 0 + (-128100093/10000000000 : ℝ)*x 1 + (4110992413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2781687547/10000000000 : ℝ)^87 ≤ (20848847760811/100000000000000 : ℝ)^71 := by
    have hnat : (2781687547 : ℕ)^87*100000000000000^71 ≤ 20848847760811^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781687547 10000000000 20848847760811 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128100093/10000000000 : ℝ)^87 ≤ (479823721009/100000000000000 : ℝ)^71 := by
    have hnat : (128100093 : ℕ)^87*100000000000000^71 ≤ 479823721009^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128100093 10000000000 479823721009 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4110992413/5000000000 : ℝ)^87 ≤ (39335664256321/50000000000000 : ℝ)^71 := by
    have hnat : (4110992413 : ℕ)^87*50000000000000^71 ≤ 39335664256321^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110992413 5000000000 39335664256321 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2781687547/10000000000 : ℝ), (-128100093/10000000000 : ℝ), (4110992413/5000000000 : ℝ)] ![(20848847760811/100000000000000 : ℝ), (479823721009/100000000000000 : ℝ), (39335664256321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2781687547/10000000000 : ℝ)|^87 ≤ (20848847760811/100000000000000 : ℝ)^71
        have hw : |(2781687547/10000000000 : ℝ)|=(2781687547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128100093/10000000000 : ℝ)|^87 ≤ (479823721009/100000000000000 : ℝ)^71
        have hw : |(-128100093/10000000000 : ℝ)|=(128100093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4110992413/5000000000 : ℝ)|^87 ≤ (39335664256321/50000000000000 : ℝ)^71
        have hw : |(4110992413/5000000000 : ℝ)|=(4110992413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-60801/625000000 : ℝ)*x 0 + (-4257572529/10000000000 : ℝ)*x 1 + (70249229/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60801/625000000 : ℝ)^87 ≤ (60658959/5000000000000 : ℝ)^71 := by
    have hnat : (60801 : ℕ)^87*5000000000000^71 ≤ 60658959^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60801 625000000 60658959 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4257572529/10000000000 : ℝ)^87 ≤ (35123108126291/100000000000000 : ℝ)^71 := by
    have hnat : (4257572529 : ℕ)^87*100000000000000^71 ≤ 35123108126291^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257572529 10000000000 35123108126291 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70249229/100000000 : ℝ)^87 ≤ (12975135736627/20000000000000 : ℝ)^71 := by
    have hnat : (70249229 : ℕ)^87*20000000000000^71 ≤ 12975135736627^71*100000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70249229 100000000 12975135736627 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60801/625000000 : ℝ), (-4257572529/10000000000 : ℝ), (70249229/100000000 : ℝ)] ![(60658959/5000000000000 : ℝ), (35123108126291/100000000000000 : ℝ), (12975135736627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60801/625000000 : ℝ)|^87 ≤ (60658959/5000000000000 : ℝ)^71
        have hw : |(-60801/625000000 : ℝ)|=(60801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4257572529/10000000000 : ℝ)|^87 ≤ (35123108126291/100000000000000 : ℝ)^71
        have hw : |(-4257572529/10000000000 : ℝ)|=(4257572529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70249229/100000000 : ℝ)|^87 ≤ (12975135736627/20000000000000 : ℝ)^71
        have hw : |(70249229/100000000 : ℝ)|=(70249229/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8484456563/10000000000 : ℝ)*x 0 + (2244537697/10000000000 : ℝ)*x 1 + (8915303/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8484456563/10000000000 : ℝ)^87 ≤ (81759702984883/100000000000000 : ℝ)^71 := by
    have hnat : (8484456563 : ℕ)^87*100000000000000^71 ≤ 81759702984883^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8484456563 10000000000 81759702984883 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244537697/10000000000 : ℝ)^87 ≤ (16028835825207/100000000000000 : ℝ)^71 := by
    have hnat : (2244537697 : ℕ)^87*100000000000000^71 ≤ 16028835825207^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244537697 10000000000 16028835825207 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8915303/200000000 : ℝ)^87 ≤ (2211461182443/100000000000000 : ℝ)^71 := by
    have hnat : (8915303 : ℕ)^87*100000000000000^71 ≤ 2211461182443^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8915303 200000000 2211461182443 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8484456563/10000000000 : ℝ), (2244537697/10000000000 : ℝ), (8915303/200000000 : ℝ)] ![(81759702984883/100000000000000 : ℝ), (16028835825207/100000000000000 : ℝ), (2211461182443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8484456563/10000000000 : ℝ)|^87 ≤ (81759702984883/100000000000000 : ℝ)^71
        have hw : |(8484456563/10000000000 : ℝ)|=(8484456563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244537697/10000000000 : ℝ)|^87 ≤ (16028835825207/100000000000000 : ℝ)^71
        have hw : |(2244537697/10000000000 : ℝ)|=(2244537697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8915303/200000000 : ℝ)|^87 ≤ (2211461182443/100000000000000 : ℝ)^71
        have hw : |(8915303/200000000 : ℝ)|=(8915303/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7761740469/10000000000 : ℝ)*x 0 + (-595027563/2500000000 : ℝ)*x 1 + (-1460506473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7761740469/10000000000 : ℝ)^87 ≤ (14661930861621/20000000000000 : ℝ)^71 := by
    have hnat : (7761740469 : ℕ)^87*20000000000000^71 ≤ 14661930861621^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7761740469 10000000000 14661930861621 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595027563/2500000000 : ℝ)^87 ≤ (688924929001/4000000000000 : ℝ)^71 := by
    have hnat : (595027563 : ℕ)^87*4000000000000^71 ≤ 688924929001^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595027563 2500000000 688924929001 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460506473/10000000000 : ℝ)^87 ≤ (189344448907/2000000000000 : ℝ)^71 := by
    have hnat : (1460506473 : ℕ)^87*2000000000000^71 ≤ 189344448907^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460506473 10000000000 189344448907 2000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7761740469/10000000000 : ℝ), (-595027563/2500000000 : ℝ), (-1460506473/10000000000 : ℝ)] ![(14661930861621/20000000000000 : ℝ), (688924929001/4000000000000 : ℝ), (189344448907/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7761740469/10000000000 : ℝ)|^87 ≤ (14661930861621/20000000000000 : ℝ)^71
        have hw : |(7761740469/10000000000 : ℝ)|=(7761740469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-595027563/2500000000 : ℝ)|^87 ≤ (688924929001/4000000000000 : ℝ)^71
        have hw : |(-595027563/2500000000 : ℝ)|=(595027563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1460506473/10000000000 : ℝ)|^87 ≤ (189344448907/2000000000000 : ℝ)^71
        have hw : |(-1460506473/10000000000 : ℝ)|=(1460506473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (63139173/312500000 : ℝ)*x 0 + (-1276050959/10000000000 : ℝ)*x 1 + (101936453/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63139173/312500000 : ℝ)^87 ≤ (7045313237251/50000000000000 : ℝ)^71 := by
    have hnat : (63139173 : ℕ)^87*50000000000000^71 ≤ 7045313237251^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63139173 312500000 7045313237251 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276050959/10000000000 : ℝ)^87 ≤ (4011838958953/50000000000000 : ℝ)^71 := by
    have hnat : (1276050959 : ℕ)^87*50000000000000^71 ≤ 4011838958953^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276050959 10000000000 4011838958953 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101936453/125000000 : ℝ)^87 ≤ (77885695600851/100000000000000 : ℝ)^71 := by
    have hnat : (101936453 : ℕ)^87*100000000000000^71 ≤ 77885695600851^71*125000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101936453 125000000 77885695600851 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63139173/312500000 : ℝ), (-1276050959/10000000000 : ℝ), (101936453/125000000 : ℝ)] ![(7045313237251/50000000000000 : ℝ), (4011838958953/50000000000000 : ℝ), (77885695600851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63139173/312500000 : ℝ)|^87 ≤ (7045313237251/50000000000000 : ℝ)^71
        have hw : |(63139173/312500000 : ℝ)|=(63139173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1276050959/10000000000 : ℝ)|^87 ≤ (4011838958953/50000000000000 : ℝ)^71
        have hw : |(-1276050959/10000000000 : ℝ)|=(1276050959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101936453/125000000 : ℝ)|^87 ≤ (77885695600851/100000000000000 : ℝ)^71
        have hw : |(101936453/125000000 : ℝ)|=(101936453/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (31/10000000000 : ℝ)*x 0 + (-8574006607/10000000000 : ℝ)*x 1 + (593857603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31/10000000000 : ℝ)^87 ≤ (3/80000000000 : ℝ)^71 := by
    have hnat : (31 : ℕ)^87*80000000000^71 ≤ 3^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31 10000000000 3 80000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8574006607/10000000000 : ℝ)^87 ≤ (41409181805123/50000000000000 : ℝ)^71 := by
    have hnat : (8574006607 : ℕ)^87*50000000000000^71 ≤ 41409181805123^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8574006607 10000000000 41409181805123 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593857603/2500000000 : ℝ)^87 ≤ (1718163637449/10000000000000 : ℝ)^71 := by
    have hnat : (593857603 : ℕ)^87*10000000000000^71 ≤ 1718163637449^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593857603 2500000000 1718163637449 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31/10000000000 : ℝ), (-8574006607/10000000000 : ℝ), (593857603/2500000000 : ℝ)] ![(3/80000000000 : ℝ), (41409181805123/50000000000000 : ℝ), (1718163637449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31/10000000000 : ℝ)|^87 ≤ (3/80000000000 : ℝ)^71
        have hw : |(31/10000000000 : ℝ)|=(31/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8574006607/10000000000 : ℝ)|^87 ≤ (41409181805123/50000000000000 : ℝ)^71
        have hw : |(-8574006607/10000000000 : ℝ)|=(8574006607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(593857603/2500000000 : ℝ)|^87 ≤ (1718163637449/10000000000000 : ℝ)^71
        have hw : |(593857603/2500000000 : ℝ)|=(593857603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8505215669/10000000000 : ℝ)*x 0 + (36390747/250000000 : ℝ)*x 1 + (1346088873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8505215669/10000000000 : ℝ)^87 ≤ (82004893949483/100000000000000 : ℝ)^71 := by
    have hnat : (8505215669 : ℕ)^87*100000000000000^71 ≤ 82004893949483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8505215669 10000000000 82004893949483 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36390747/250000000 : ℝ)^87 ≤ (4714251329731/50000000000000 : ℝ)^71 := by
    have hnat : (36390747 : ℕ)^87*50000000000000^71 ≤ 4714251329731^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36390747 250000000 4714251329731 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346088873/10000000000 : ℝ)^87 ≤ (8566603382567/100000000000000 : ℝ)^71 := by
    have hnat : (1346088873 : ℕ)^87*100000000000000^71 ≤ 8566603382567^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346088873 10000000000 8566603382567 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8505215669/10000000000 : ℝ), (36390747/250000000 : ℝ), (1346088873/10000000000 : ℝ)] ![(82004893949483/100000000000000 : ℝ), (4714251329731/50000000000000 : ℝ), (8566603382567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8505215669/10000000000 : ℝ)|^87 ≤ (82004893949483/100000000000000 : ℝ)^71
        have hw : |(8505215669/10000000000 : ℝ)|=(8505215669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36390747/250000000 : ℝ)|^87 ≤ (4714251329731/50000000000000 : ℝ)^71
        have hw : |(36390747/250000000 : ℝ)|=(36390747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346088873/10000000000 : ℝ)|^87 ≤ (8566603382567/100000000000000 : ℝ)^71
        have hw : |(1346088873/10000000000 : ℝ)|=(1346088873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (695949367/2500000000 : ℝ)*x 0 + (-5044196977/10000000000 : ℝ)*x 1 + (-4334148887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695949367/2500000000 : ℝ)^87 ≤ (417364541067/2000000000000 : ℝ)^71 := by
    have hnat : (695949367 : ℕ)^87*2000000000000^71 ≤ 417364541067^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695949367 2500000000 417364541067 2000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044196977/10000000000 : ℝ)^87 ≤ (43233022137631/100000000000000 : ℝ)^71 := by
    have hnat : (5044196977 : ℕ)^87*100000000000000^71 ≤ 43233022137631^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044196977 10000000000 43233022137631 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4334148887/10000000000 : ℝ)^87 ≤ (89746876991/250000000000 : ℝ)^71 := by
    have hnat : (4334148887 : ℕ)^87*250000000000^71 ≤ 89746876991^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334148887 10000000000 89746876991 250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(695949367/2500000000 : ℝ), (-5044196977/10000000000 : ℝ), (-4334148887/10000000000 : ℝ)] ![(417364541067/2000000000000 : ℝ), (43233022137631/100000000000000 : ℝ), (89746876991/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(695949367/2500000000 : ℝ)|^87 ≤ (417364541067/2000000000000 : ℝ)^71
        have hw : |(695949367/2500000000 : ℝ)|=(695949367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5044196977/10000000000 : ℝ)|^87 ≤ (43233022137631/100000000000000 : ℝ)^71
        have hw : |(-5044196977/10000000000 : ℝ)|=(5044196977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4334148887/10000000000 : ℝ)|^87 ≤ (89746876991/250000000000 : ℝ)^71
        have hw : |(-4334148887/10000000000 : ℝ)|=(4334148887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7049445187/10000000000 : ℝ)*x 0 + (-699335429/10000000000 : ℝ)*x 1 + (3845748973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7049445187/10000000000 : ℝ)^87 ≤ (6515328724629/10000000000000 : ℝ)^71 := by
    have hnat : (7049445187 : ℕ)^87*10000000000000^71 ≤ 6515328724629^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7049445187 10000000000 6515328724629 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699335429/10000000000 : ℝ)^87 ≤ (1920007735427/50000000000000 : ℝ)^71 := by
    have hnat : (699335429 : ℕ)^87*50000000000000^71 ≤ 1920007735427^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699335429 10000000000 1920007735427 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3845748973/10000000000 : ℝ)^87 ≤ (775167431799/2500000000000 : ℝ)^71 := by
    have hnat : (3845748973 : ℕ)^87*2500000000000^71 ≤ 775167431799^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845748973 10000000000 775167431799 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7049445187/10000000000 : ℝ), (-699335429/10000000000 : ℝ), (3845748973/10000000000 : ℝ)] ![(6515328724629/10000000000000 : ℝ), (1920007735427/50000000000000 : ℝ), (775167431799/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7049445187/10000000000 : ℝ)|^87 ≤ (6515328724629/10000000000000 : ℝ)^71
        have hw : |(7049445187/10000000000 : ℝ)|=(7049445187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-699335429/10000000000 : ℝ)|^87 ≤ (1920007735427/50000000000000 : ℝ)^71
        have hw : |(-699335429/10000000000 : ℝ)|=(699335429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3845748973/10000000000 : ℝ)|^87 ≤ (775167431799/2500000000000 : ℝ)^71
        have hw : |(3845748973/10000000000 : ℝ)|=(3845748973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-786649143/10000000000 : ℝ)*x 0 + (-5572946901/10000000000 : ℝ)*x 1 + (2686656467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786649143/10000000000 : ℝ)^87 ≤ (2217752157123/50000000000000 : ℝ)^71 := by
    have hnat : (786649143 : ℕ)^87*50000000000000^71 ≤ 2217752157123^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786649143 10000000000 2217752157123 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5572946901/10000000000 : ℝ)^87 ≤ (48850003823797/100000000000000 : ℝ)^71 := by
    have hnat : (5572946901 : ℕ)^87*100000000000000^71 ≤ 48850003823797^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572946901 10000000000 48850003823797 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2686656467/5000000000 : ℝ)^87 ≤ (23357245920927/50000000000000 : ℝ)^71 := by
    have hnat : (2686656467 : ℕ)^87*50000000000000^71 ≤ 23357245920927^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686656467 5000000000 23357245920927 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-786649143/10000000000 : ℝ), (-5572946901/10000000000 : ℝ), (2686656467/5000000000 : ℝ)] ![(2217752157123/50000000000000 : ℝ), (48850003823797/100000000000000 : ℝ), (23357245920927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-786649143/10000000000 : ℝ)|^87 ≤ (2217752157123/50000000000000 : ℝ)^71
        have hw : |(-786649143/10000000000 : ℝ)|=(786649143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5572946901/10000000000 : ℝ)|^87 ≤ (48850003823797/100000000000000 : ℝ)^71
        have hw : |(-5572946901/10000000000 : ℝ)|=(5572946901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2686656467/5000000000 : ℝ)|^87 ≤ (23357245920927/50000000000000 : ℝ)^71
        have hw : |(2686656467/5000000000 : ℝ)|=(2686656467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5694182287/10000000000 : ℝ)*x 0 + (3282895367/10000000000 : ℝ)*x 1 + (394053961/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5694182287/10000000000 : ℝ)^87 ≤ (50155354882349/100000000000000 : ℝ)^71 := by
    have hnat : (5694182287 : ℕ)^87*100000000000000^71 ≤ 50155354882349^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5694182287 10000000000 50155354882349 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3282895367/10000000000 : ℝ)^87 ≤ (25541390866533/100000000000000 : ℝ)^71 := by
    have hnat : (3282895367 : ℕ)^87*100000000000000^71 ≤ 25541390866533^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282895367 10000000000 25541390866533 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394053961/1250000000 : ℝ)^87 ≤ (4860650847821/20000000000000 : ℝ)^71 := by
    have hnat : (394053961 : ℕ)^87*20000000000000^71 ≤ 4860650847821^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394053961 1250000000 4860650847821 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5694182287/10000000000 : ℝ), (3282895367/10000000000 : ℝ), (394053961/1250000000 : ℝ)] ![(50155354882349/100000000000000 : ℝ), (25541390866533/100000000000000 : ℝ), (4860650847821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5694182287/10000000000 : ℝ)|^87 ≤ (50155354882349/100000000000000 : ℝ)^71
        have hw : |(5694182287/10000000000 : ℝ)|=(5694182287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3282895367/10000000000 : ℝ)|^87 ≤ (25541390866533/100000000000000 : ℝ)^71
        have hw : |(3282895367/10000000000 : ℝ)|=(3282895367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394053961/1250000000 : ℝ)|^87 ≤ (4860650847821/20000000000000 : ℝ)^71
        have hw : |(394053961/1250000000 : ℝ)|=(394053961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54005339/100000000 : ℝ)*x 0 + (-431954711/1250000000 : ℝ)*x 1 + (-827434027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54005339/100000000 : ℝ)^87 ≤ (47004641082537/100000000000000 : ℝ)^71 := by
    have hnat : (54005339 : ℕ)^87*100000000000000^71 ≤ 47004641082537^71*100000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54005339 100000000 47004641082537 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431954711/1250000000 : ℝ)^87 ≤ (849932779183/3125000000000 : ℝ)^71 := by
    have hnat : (431954711 : ℕ)^87*3125000000000^71 ≤ 849932779183^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431954711 1250000000 849932779183 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827434027/2500000000 : ℝ)^87 ≤ (25797509967399/100000000000000 : ℝ)^71 := by
    have hnat : (827434027 : ℕ)^87*100000000000000^71 ≤ 25797509967399^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827434027 2500000000 25797509967399 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54005339/100000000 : ℝ), (-431954711/1250000000 : ℝ), (-827434027/2500000000 : ℝ)] ![(47004641082537/100000000000000 : ℝ), (849932779183/3125000000000 : ℝ), (25797509967399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54005339/100000000 : ℝ)|^87 ≤ (47004641082537/100000000000000 : ℝ)^71
        have hw : |(54005339/100000000 : ℝ)|=(54005339/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431954711/1250000000 : ℝ)|^87 ≤ (849932779183/3125000000000 : ℝ)^71
        have hw : |(-431954711/1250000000 : ℝ)|=(431954711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-827434027/2500000000 : ℝ)|^87 ≤ (25797509967399/100000000000000 : ℝ)^71
        have hw : |(-827434027/2500000000 : ℝ)|=(827434027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325086_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4452990109/10000000000 : ℝ)*x 0 + (-3159359931/10000000000 : ℝ)*x 1 + (918198327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452990109/10000000000 : ℝ)^87 ≤ (3710860731999/10000000000000 : ℝ)^71 := by
    have hnat : (4452990109 : ℕ)^87*10000000000000^71 ≤ 3710860731999^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452990109 10000000000 3710860731999 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3159359931/10000000000 : ℝ)^87 ≤ (1218435969949/5000000000000 : ℝ)^71 := by
    have hnat : (3159359931 : ℕ)^87*5000000000000^71 ≤ 1218435969949^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3159359931 10000000000 1218435969949 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (918198327/2000000000 : ℝ)^87 ≤ (2407667079617/6250000000000 : ℝ)^71 := by
    have hnat : (918198327 : ℕ)^87*6250000000000^71 ≤ 2407667079617^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918198327 2000000000 2407667079617 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452990109/10000000000 : ℝ), (-3159359931/10000000000 : ℝ), (918198327/2000000000 : ℝ)] ![(3710860731999/10000000000000 : ℝ), (1218435969949/5000000000000 : ℝ), (2407667079617/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452990109/10000000000 : ℝ)|^87 ≤ (3710860731999/10000000000000 : ℝ)^71
        have hw : |(4452990109/10000000000 : ℝ)|=(4452990109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3159359931/10000000000 : ℝ)|^87 ≤ (1218435969949/5000000000000 : ℝ)^71
        have hw : |(-3159359931/10000000000 : ℝ)|=(3159359931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(918198327/2000000000 : ℝ)|^87 ≤ (2407667079617/6250000000000 : ℝ)^71
        have hw : |(918198327/2000000000 : ℝ)|=(918198327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325086 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((310241533/500000000 : ℝ)*X 1 0+(1493521889/5000000000 : ℝ)*X 1 1+(57109347/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2935279501/5000000000 : ℝ)*X 2 0+(-3217788899/10000000000 : ℝ)*X 2 1+(-188443319/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3448807073/10000000000 : ℝ)*X 0 0+(-2141287409/10000000000 : ℝ)*X 0 1+(255499723/400000000 : ℝ)*X 0 2+(3448807073/10000000000 : ℝ)*X 1 0+(-2141287409/10000000000 : ℝ)*X 1 1+(255499723/400000000 : ℝ)*X 1 2+(3448807073/10000000000 : ℝ)*X 2 0+(-2141287409/10000000000 : ℝ)*X 2 1+(255499723/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-206353/10000000000 : ℝ)*X 0 0+(-4218159589/5000000000 : ℝ)*X 0 1+(127870341/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((966238999/2000000000 : ℝ)*X 1 0+(508263103/1000000000 : ℝ)*X 1 1+(216736981/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5792534981/10000000000 : ℝ)*X 2 0+(-2866242799/10000000000 : ℝ)*X 2 1+(-3450987577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2781687547/10000000000 : ℝ)*X 0 0+(-128100093/10000000000 : ℝ)*X 0 1+(4110992413/5000000000 : ℝ)*X 0 2+(2781687547/10000000000 : ℝ)*X 1 0+(-128100093/10000000000 : ℝ)*X 1 1+(4110992413/5000000000 : ℝ)*X 1 2+(2781687547/10000000000 : ℝ)*X 2 0+(-128100093/10000000000 : ℝ)*X 2 1+(4110992413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-60801/625000000 : ℝ)*X 0 0+(-4257572529/10000000000 : ℝ)*X 0 1+(70249229/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8484456563/10000000000 : ℝ)*X 1 0+(2244537697/10000000000 : ℝ)*X 1 1+(8915303/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7761740469/10000000000 : ℝ)*X 2 0+(-595027563/2500000000 : ℝ)*X 2 1+(-1460506473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((63139173/312500000 : ℝ)*X 0 0+(-1276050959/10000000000 : ℝ)*X 0 1+(101936453/125000000 : ℝ)*X 0 2+(63139173/312500000 : ℝ)*X 1 0+(-1276050959/10000000000 : ℝ)*X 1 1+(101936453/125000000 : ℝ)*X 1 2+(63139173/312500000 : ℝ)*X 2 0+(-1276050959/10000000000 : ℝ)*X 2 1+(101936453/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((31/10000000000 : ℝ)*X 0 0+(-8574006607/10000000000 : ℝ)*X 0 1+(593857603/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8505215669/10000000000 : ℝ)*X 1 0+(36390747/250000000 : ℝ)*X 1 1+(1346088873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((695949367/2500000000 : ℝ)*X 2 0+(-5044196977/10000000000 : ℝ)*X 2 1+(-4334148887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7049445187/10000000000 : ℝ)*X 0 0+(-699335429/10000000000 : ℝ)*X 0 1+(3845748973/10000000000 : ℝ)*X 0 2+(7049445187/10000000000 : ℝ)*X 1 0+(-699335429/10000000000 : ℝ)*X 1 1+(3845748973/10000000000 : ℝ)*X 1 2+(7049445187/10000000000 : ℝ)*X 2 0+(-699335429/10000000000 : ℝ)*X 2 1+(3845748973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((54119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19593978197713336632339/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199494024853/250000000000 : ℝ)*(base7) + (3868333/500000000000 : ℝ)*(base17) + (1798919/1000000000000 : ℝ)*(base43) + (1364029/1000000000000 : ℝ)*(base50) + (211271514209/500000000000 : ℝ)*(base54) + (1788371029661/1000000000000 : ℝ)*(major_s0_0) + (894184615371/500000000000 : ℝ)*(major_s0_1) + (1365828001243/1000000000000 : ℝ)*(major_s0_2) + (597539/500000000000 : ℝ)*(sp_s0_6) + (2246926188393/1000000000000 : ℝ)*(sp_s0_7) + (1123460125323/500000000000 : ℝ)*(sp_s0_8) + (72975326399/40000000000 : ℝ)*(sp_s0_9) + (1265418177779/1000000000000 : ℝ)*(sp_s0_13) + (1031521/50000000000 : ℝ)*(sp_s0_20) + (890006932283/1000000000000 : ℝ)*(f.failure) + (140432999207/62500000000 : ℝ)*(f.sum) + (209369399480633/2000000000000000000000000000 : ℝ)*base62 + (2522865470974067/10000000000000000000000000000 : ℝ)*base65 + (80597707742599/5000000000000000000000000000 : ℝ)*base66 + (1630126257391767/10000000000000000000000000000 : ℝ)*base68 + (1001841167267271/5000000000000000000000000000 : ℝ)*base70 + (1446668656440709/10000000000000000000000000000 : ℝ)*base72 + (275626820505699/5000000000000000000000000000 : ℝ)*base74 + (193552317508609/10000000000000000000000000000 : ℝ)*base76 + (3810691127074093/10000000000000000000000000000 : ℝ)*base79 + (86263/100000000000000000 : ℝ)*base86 + (86263/100000000000000000 : ℝ)*base88 + (86263/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-67403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-67403/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40149302941089384099441/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1189739514521/1000000000000 : ℝ)*(base7) + (2376833/1000000000000 : ℝ)*(base31) + (936043/125000000000 : ℝ)*(base33) + (14137/250000000000 : ℝ)*(base54) + (43378492853/1000000000000 : ℝ)*(base60) + (1523748410041/1000000000000 : ℝ)*(major_s0_0) + (304751179677/200000000000 : ℝ)*(major_s0_1) + (1523755841837/1000000000000 : ℝ)*(major_s0_2) + (13233679/1000000000000 : ℝ)*(sp_s0_1) + (1633463862263/1000000000000 : ℝ)*(sp_s0_14) + (816683311273/500000000000 : ℝ)*(sp_s0_15) + (1633456317371/1000000000000 : ℝ)*(sp_s0_16) + (121753420561/62500000000 : ℝ)*(sp_s0_20) + (38258847/500000000000 : ℝ)*(sp_s0_22) + (189579411959/250000000000 : ℝ)*(f.failure) + (1633463862263/1000000000000 : ℝ)*(f.sum) + (1952063256526091/5000000000000000000000000000 : ℝ)*base63 + (1876878576346453/10000000000000000000000000000 : ℝ)*base65 + (211531873731713/2000000000000000000000000000 : ℝ)*base66 + (3628015389859247/10000000000000000000000000000 : ℝ)*base69 + (528722524078953/1250000000000000000000000000 : ℝ)*base71 + (248547594035071/10000000000000000000000000000 : ℝ)*base73 + (728761511238587/2000000000000000000000000000 : ℝ)*base75 + (2946637236714829/10000000000000000000000000000 : ℝ)*base76 + (125597530188253/5000000000000000000000000000 : ℝ)*base79 + (4501/25000000000000000 : ℝ)*base87 + (4501/25000000000000000 : ℝ)*base89 + (4501/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68113/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68113/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3444061251324243749331/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5415940971/5000000000 : ℝ)*(base7) + (5314041163/125000000000 : ℝ)*(base40) + (57780911803/100000000000 : ℝ)*(base43) + (2560817/1000000000000 : ℝ)*(base50) + (1521134668957/1000000000000 : ℝ)*(major_s0_0) + (943325550927/1000000000000 : ℝ)*(major_s0_1) + (1521134668957/1000000000000 : ℝ)*(major_s0_2) + (998999/40000000000 : ℝ)*(sp_s0_2) + (257871289/1000000000000 : ℝ)*(sp_s0_7) + (5074347/500000000000 : ℝ)*(sp_s0_9) + (69386517347/62500000000 : ℝ)*(sp_s0_21) + (1688251266871/1000000000000 : ℝ)*(sp_s0_22) + (1110407025173/1000000000000 : ℝ)*(sp_s0_23) + (1840201351903/1000000000000 : ℝ)*(sp_s0_27) + (757013157703/1000000000000 : ℝ)*(f.failure) + (1688251266871/1000000000000 : ℝ)*(f.sum) + (658855370780663/1250000000000000000000000000 : ℝ)*base63 + (2925277094110267/10000000000000000000000000000 : ℝ)*base64 + (1697256092152037/10000000000000000000000000000 : ℝ)*base67 + (4282926887747967/10000000000000000000000000000 : ℝ)*base69 + (6863203676377/100000000000000000000000000 : ℝ)*base71 + (4225342985110267/10000000000000000000000000000 : ℝ)*base73 + (5032876885497337/10000000000000000000000000000 : ℝ)*base75 + (3187899886747967/10000000000000000000000000000 : ℝ)*base77 + (2948524133197/312500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (16883/100000000000000000 : ℝ)*base86 + (16883/100000000000000000 : ℝ)*base88 + (16883/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (54119/100000 : ℝ) ^ (85/16 : ℝ) ≤ (1915978455587967879/50000000000000000000 : ℝ) := by
    have hpowers : (54119/100000 : ℝ)^85 ≤ (1915978455587967879/50000000000000000000 : ℝ)^16 := by
      have hnat : (54119 : ℕ)^85*50000000000000000000^16 ≤ 1915978455587967879^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54119 100000 1915978455587967879 50000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54119/100000 : ℝ)) (X := (1915978455587967879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51915978455587967879/50000000000000000000 : ℝ) ≤ (10071034366630987/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (51915978455587967879/50000000000000000000 : ℝ)^16 ≤ (10071034366630987/10000000000000000 : ℝ)^85 := by
      have hnat : (51915978455587967879 : ℕ)^16*10000000000000000^85 ≤ 10071034366630987^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51915978455587967879 50000000000000000000 10071034366630987 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10071034366630987/10000000000000000 : ℝ)) (X := (51915978455587967879/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26915978455587967879/25000000000000000000 : ℝ) ≤ (1267496444161291/1250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (26915978455587967879/25000000000000000000 : ℝ)^16 ≤ (1267496444161291/1250000000000000 : ℝ)^85 := by
      have hnat : (26915978455587967879 : ℕ)^16*1250000000000000^85 ≤ 1267496444161291^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26915978455587967879 25000000000000000000 1267496444161291 1250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1267496444161291/1250000000000000 : ℝ)) (X := (26915978455587967879/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(71034366630987/5411900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5302860512257/416300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (54119/100000 : ℝ)) (alpha := (71034366630987/5411900000000000 : ℝ)) (beta := (5302860512257/416300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (54119/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(71034366630987/5411900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5302860512257/416300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (67403/100000 : ℝ) ^ (85/16 : ℝ) ≤ (3074669222824375473/25000000000000000000 : ℝ) := by
    have hpowers : (67403/100000 : ℝ)^85 ≤ (3074669222824375473/25000000000000000000 : ℝ)^16 := by
      have hnat : (67403 : ℕ)^85*25000000000000000000^16 ≤ 3074669222824375473^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67403 100000 3074669222824375473 25000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67403/100000 : ℝ)) (X := (3074669222824375473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (28074669222824375473/25000000000000000000 : ℝ) ≤ (2555184673025127/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (28074669222824375473/25000000000000000000 : ℝ)^16 ≤ (2555184673025127/2500000000000000 : ℝ)^85 := by
      have hnat : (28074669222824375473 : ℕ)^16*2500000000000000^85 ≤ 2555184673025127^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28074669222824375473 25000000000000000000 2555184673025127 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2555184673025127/2500000000000000 : ℝ)) (X := (28074669222824375473/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15574669222824375473/12500000000000000000 : ℝ) ≤ (1302831179519921/1250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (15574669222824375473/12500000000000000000 : ℝ)^16 ≤ (1302831179519921/1250000000000000 : ℝ)^85 := by
      have hnat : (15574669222824375473 : ℕ)^16*1250000000000000^85 ≤ 1302831179519921^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15574669222824375473 12500000000000000000 1302831179519921 1250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1302831179519921/1250000000000000 : ℝ)) (X := (15574669222824375473/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(55184673025127/1685075000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(10095537202943/337015000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (67403/100000 : ℝ)) (alpha := (55184673025127/1685075000000000 : ℝ)) (beta := (10095537202943/337015000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (67403/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(55184673025127/1685075000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(10095537202943/337015000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (68113/100000 : ℝ) ^ (85/16 : ℝ) ≤ (325068158734692921/2500000000000000000 : ℝ) := by
    have hpowers : (68113/100000 : ℝ)^85 ≤ (325068158734692921/2500000000000000000 : ℝ)^16 := by
      have hnat : (68113 : ℕ)^85*2500000000000000000^16 ≤ 325068158734692921^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68113 100000 325068158734692921 2500000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68113/100000 : ℝ)) (X := (325068158734692921/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (2825068158734692921/2500000000000000000 : ℝ) ≤ (159887029808117/156250000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2825068158734692921/2500000000000000000 : ℝ)^16 ≤ (159887029808117/156250000000000 : ℝ)^85 := by
      have hnat : (2825068158734692921 : ℕ)^16*156250000000000^85 ≤ 159887029808117^85*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2825068158734692921 2500000000000000000 159887029808117 156250000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (159887029808117/156250000000000 : ℝ)) (X := (2825068158734692921/2500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1575068158734692921/1250000000000000000 : ℝ) ≤ (1305590044361477/1250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (1575068158734692921/1250000000000000000 : ℝ)^16 ≤ (1305590044361477/1250000000000000 : ℝ)^85 := by
      have hnat : (1575068158734692921 : ℕ)^16*1250000000000000^85 ≤ 1305590044361477^85*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1575068158734692921 1250000000000000000 1305590044361477 1250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1305590044361477/1250000000000000 : ℝ)) (X := (1575068158734692921/1250000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3637029808117/106426562500000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(26493805896541/851412500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (68113/100000 : ℝ)) (alpha := (3637029808117/106426562500000 : ℝ)) (beta := (26493805896541/851412500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (68113/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3637029808117/106426562500000 : ℝ)*((1 : ℝ)*pair X 2 0)+(26493805896541/851412500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-786649143/10000000000 : ℝ)*X 0 0+(-5572946901/10000000000 : ℝ)*X 0 1+(2686656467/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5694182287/10000000000 : ℝ)*X 1 0+(3282895367/10000000000 : ℝ)*X 1 1+(394053961/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((54005339/100000000 : ℝ)*X 2 0+(-431954711/1250000000 : ℝ)*X 2 1+(-827434027/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4452990109/10000000000 : ℝ)*X 0 0+(-3159359931/10000000000 : ℝ)*X 0 1+(918198327/2000000000 : ℝ)*X 0 2+(4452990109/10000000000 : ℝ)*X 1 0+(-3159359931/10000000000 : ℝ)*X 1 1+(918198327/2000000000 : ℝ)*X 1 2+(4452990109/10000000000 : ℝ)*X 2 0+(-3159359931/10000000000 : ℝ)*X 2 1+(918198327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325086_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-4483688303165345689345788786726671883/496922881100282000000000000000000000 : ℝ) := by norm_num
    linear_combination (60599/200000000000 : ℝ)*(base7) + (2923/25000000000 : ℝ)*(base10) + (288009/1000000000000 : ℝ)*(base17) + (354303/1000000000000 : ℝ)*(base19) + (289271/1000000000000 : ℝ)*(base21) + (21589/1000000000000 : ℝ)*(base31) + (627749883543/1000000000000 : ℝ)*(base40) + (19960487877/250000000000 : ℝ)*(base60) + (200939/100000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (375954369249/125000000000 : ℝ)*(sp_s1_0) + (15038172143/5000000000 : ℝ)*(sp_s1_1) + (3007634781641/1000000000000 : ℝ)*(sp_s1_2) + (1000000281407/1000000000000 : ℝ)*(sp_s1_6) + (46994297983/15625000000 : ℝ)*(f.sum) + (9540794645683000727/45910205390000000000000000000000 : ℝ)*base63 + (279635895445117/681130000000000000000000000 : ℝ)*base65 + (400503007069119/674030000000000000000000000 : ℝ)*base66 + (45292294990619/681130000000000000000000000 : ℝ)*base68 + (11445460684823021499/36862074470000000000000000000000 : ℝ)*base71 + (3569787332187/8326000000000000000000000 : ℝ)*base72 + (87628599125989/674030000000000000000000000 : ℝ)*base74 + (6312301097283/21647600000000000000000000 : ℝ)*base77 + (1406136557208608513/2805986890000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b043 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c325085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c325086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b043 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
