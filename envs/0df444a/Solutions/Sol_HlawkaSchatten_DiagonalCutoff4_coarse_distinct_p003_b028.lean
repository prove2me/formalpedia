-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b028
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:55.018535+00:00
-- url     : https://prove2.me/submissions/98f7a347-1751-4969-a99e-e98dc07359aa

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
theorem collision_support_c303068_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7717852567/10000000000 : ℝ)*x 0 + (751169169/2500000000 : ℝ)*x 1 + (-1546639757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7717852567/10000000000 : ℝ)^33 ≤ (71038756550863/100000000000000 : ℝ)^25 := by
    have hnat : (7717852567 : ℕ)^33*100000000000000^25 ≤ 71038756550863^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7717852567 10000000000 71038756550863 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751169169/2500000000 : ℝ)^33 ≤ (20449986441629/100000000000000 : ℝ)^25 := by
    have hnat : (751169169 : ℕ)^33*100000000000000^25 ≤ 20449986441629^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751169169 2500000000 20449986441629 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1546639757/10000000000 : ℝ)^33 ≤ (8511256992889/100000000000000 : ℝ)^25 := by
    have hnat : (1546639757 : ℕ)^33*100000000000000^25 ≤ 8511256992889^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546639757 10000000000 8511256992889 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7717852567/10000000000 : ℝ), (751169169/2500000000 : ℝ), (-1546639757/10000000000 : ℝ)] ![(71038756550863/100000000000000 : ℝ), (20449986441629/100000000000000 : ℝ), (8511256992889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7717852567/10000000000 : ℝ)|^33 ≤ (71038756550863/100000000000000 : ℝ)^25
        have hw : |(7717852567/10000000000 : ℝ)|=(7717852567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751169169/2500000000 : ℝ)|^33 ≤ (20449986441629/100000000000000 : ℝ)^25
        have hw : |(751169169/2500000000 : ℝ)|=(751169169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1546639757/10000000000 : ℝ)|^33 ≤ (8511256992889/100000000000000 : ℝ)^25
        have hw : |(-1546639757/10000000000 : ℝ)|=(1546639757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-24878067/625000000 : ℝ)*x 0 + (-5779651781/10000000000 : ℝ)*x 1 + (-5922486613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24878067/625000000 : ℝ)^33 ≤ (2771062823/195312500000 : ℝ)^25 := by
    have hnat : (24878067 : ℕ)^33*195312500000^25 ≤ 2771062823^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24878067 625000000 2771062823 195312500000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5779651781/10000000000 : ℝ)^33 ≤ (24248239513371/50000000000000 : ℝ)^25 := by
    have hnat : (5779651781 : ℕ)^33*50000000000000^25 ≤ 24248239513371^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5779651781 10000000000 24248239513371 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5922486613/10000000000 : ℝ)^33 ≤ (12521184198459/25000000000000 : ℝ)^25 := by
    have hnat : (5922486613 : ℕ)^33*25000000000000^25 ≤ 12521184198459^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5922486613 10000000000 12521184198459 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24878067/625000000 : ℝ), (-5779651781/10000000000 : ℝ), (-5922486613/10000000000 : ℝ)] ![(2771062823/195312500000 : ℝ), (24248239513371/50000000000000 : ℝ), (12521184198459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24878067/625000000 : ℝ)|^33 ≤ (2771062823/195312500000 : ℝ)^25
        have hw : |(-24878067/625000000 : ℝ)|=(24878067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5779651781/10000000000 : ℝ)|^33 ≤ (24248239513371/50000000000000 : ℝ)^25
        have hw : |(-5779651781/10000000000 : ℝ)|=(5779651781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5922486613/10000000000 : ℝ)|^33 ≤ (12521184198459/25000000000000 : ℝ)^25
        have hw : |(-5922486613/10000000000 : ℝ)|=(5922486613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7661563867/10000000000 : ℝ)*x 0 + (3692252339/10000000000 : ℝ)*x 1 + (-666514267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7661563867/10000000000 : ℝ)^33 ≤ (70355653705417/100000000000000 : ℝ)^25 := by
    have hnat : (7661563867 : ℕ)^33*100000000000000^25 ≤ 70355653705417^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7661563867 10000000000 70355653705417 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692252339/10000000000 : ℝ)^33 ≤ (26842602122571/100000000000000 : ℝ)^25 := by
    have hnat : (3692252339 : ℕ)^33*100000000000000^25 ≤ 26842602122571^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692252339 10000000000 26842602122571 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666514267/10000000000 : ℝ)^33 ≤ (175109009503/6250000000000 : ℝ)^25 := by
    have hnat : (666514267 : ℕ)^33*6250000000000^25 ≤ 175109009503^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666514267 10000000000 175109009503 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7661563867/10000000000 : ℝ), (3692252339/10000000000 : ℝ), (-666514267/10000000000 : ℝ)] ![(70355653705417/100000000000000 : ℝ), (26842602122571/100000000000000 : ℝ), (175109009503/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7661563867/10000000000 : ℝ)|^33 ≤ (70355653705417/100000000000000 : ℝ)^25
        have hw : |(7661563867/10000000000 : ℝ)|=(7661563867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692252339/10000000000 : ℝ)|^33 ≤ (26842602122571/100000000000000 : ℝ)^25
        have hw : |(3692252339/10000000000 : ℝ)|=(3692252339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-666514267/10000000000 : ℝ)|^33 ≤ (175109009503/6250000000000 : ℝ)^25
        have hw : |(-666514267/10000000000 : ℝ)|=(666514267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (460545821/1000000000 : ℝ)*x 0 + (-718410811/2500000000 : ℝ)*x 1 + (544122943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460545821/1000000000 : ℝ)^33 ≤ (17967603733471/50000000000000 : ℝ)^25 := by
    have hnat : (460545821 : ℕ)^33*50000000000000^25 ≤ 17967603733471^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460545821 1000000000 17967603733471 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718410811/2500000000 : ℝ)^33 ≤ (19281080270533/100000000000000 : ℝ)^25 := by
    have hnat : (718410811 : ℕ)^33*100000000000000^25 ≤ 19281080270533^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718410811 2500000000 19281080270533 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544122943/1000000000 : ℝ)^33 ≤ (22391856124639/50000000000000 : ℝ)^25 := by
    have hnat : (544122943 : ℕ)^33*50000000000000^25 ≤ 22391856124639^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544122943 1000000000 22391856124639 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(460545821/1000000000 : ℝ), (-718410811/2500000000 : ℝ), (544122943/1000000000 : ℝ)] ![(17967603733471/50000000000000 : ℝ), (19281080270533/100000000000000 : ℝ), (22391856124639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(460545821/1000000000 : ℝ)|^33 ≤ (17967603733471/50000000000000 : ℝ)^25
        have hw : |(460545821/1000000000 : ℝ)|=(460545821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-718410811/2500000000 : ℝ)|^33 ≤ (19281080270533/100000000000000 : ℝ)^25
        have hw : |(-718410811/2500000000 : ℝ)|=(718410811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544122943/1000000000 : ℝ)|^33 ≤ (22391856124639/50000000000000 : ℝ)^25
        have hw : |(544122943/1000000000 : ℝ)|=(544122943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (540590967/1000000000 : ℝ)*x 0 + (-111331423/1000000000 : ℝ)*x 1 + (-5922486613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540590967/1000000000 : ℝ)^33 ≤ (44400391104509/100000000000000 : ℝ)^25 := by
    have hnat : (540590967 : ℕ)^33*100000000000000^25 ≤ 44400391104509^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540590967 1000000000 44400391104509 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111331423/1000000000 : ℝ)^33 ≤ (275743604069/5000000000000 : ℝ)^25 := by
    have hnat : (111331423 : ℕ)^33*5000000000000^25 ≤ 275743604069^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111331423 1000000000 275743604069 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5922486613/10000000000 : ℝ)^33 ≤ (12521184198459/25000000000000 : ℝ)^25 := by
    have hnat : (5922486613 : ℕ)^33*25000000000000^25 ≤ 12521184198459^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5922486613 10000000000 12521184198459 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540590967/1000000000 : ℝ), (-111331423/1000000000 : ℝ), (-5922486613/10000000000 : ℝ)] ![(44400391104509/100000000000000 : ℝ), (275743604069/5000000000000 : ℝ), (12521184198459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540590967/1000000000 : ℝ)|^33 ≤ (44400391104509/100000000000000 : ℝ)^25
        have hw : |(540590967/1000000000 : ℝ)|=(540590967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111331423/1000000000 : ℝ)|^33 ≤ (275743604069/5000000000000 : ℝ)^25
        have hw : |(-111331423/1000000000 : ℝ)|=(111331423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5922486613/10000000000 : ℝ)|^33 ≤ (12521184198459/25000000000000 : ℝ)^25
        have hw : |(-5922486613/10000000000 : ℝ)|=(5922486613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-136828353/10000000000 : ℝ)*x 0 + (-1060063207/2500000000 : ℝ)*x 1 + (-7419057851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136828353/10000000000 : ℝ)^33 ≤ (10829352063/3125000000000 : ℝ)^25 := by
    have hnat : (136828353 : ℕ)^33*3125000000000^25 ≤ 10829352063^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136828353 10000000000 10829352063 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060063207/2500000000 : ℝ)^33 ≤ (32222342773859/100000000000000 : ℝ)^25 := by
    have hnat : (1060063207 : ℕ)^33*100000000000000^25 ≤ 32222342773859^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060063207 2500000000 32222342773859 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7419057851/10000000000 : ℝ)^33 ≤ (33715558975829/50000000000000 : ℝ)^25 := by
    have hnat : (7419057851 : ℕ)^33*50000000000000^25 ≤ 33715558975829^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7419057851 10000000000 33715558975829 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136828353/10000000000 : ℝ), (-1060063207/2500000000 : ℝ), (-7419057851/10000000000 : ℝ)] ![(10829352063/3125000000000 : ℝ), (32222342773859/100000000000000 : ℝ), (33715558975829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136828353/10000000000 : ℝ)|^33 ≤ (10829352063/3125000000000 : ℝ)^25
        have hw : |(-136828353/10000000000 : ℝ)|=(136828353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060063207/2500000000 : ℝ)|^33 ≤ (32222342773859/100000000000000 : ℝ)^25
        have hw : |(-1060063207/2500000000 : ℝ)|=(1060063207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7419057851/10000000000 : ℝ)|^33 ≤ (33715558975829/50000000000000 : ℝ)^25
        have hw : |(-7419057851/10000000000 : ℝ)|=(7419057851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9299213293/10000000000 : ℝ)*x 0 + (185021841/1250000000 : ℝ)*x 1 + (-165611207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9299213293/10000000000 : ℝ)^33 ≤ (45427517079983/50000000000000 : ℝ)^25 := by
    have hnat : (9299213293 : ℕ)^33*50000000000000^25 ≤ 45427517079983^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9299213293 10000000000 45427517079983 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185021841/1250000000 : ℝ)^33 ≤ (8031804707821/100000000000000 : ℝ)^25 := by
    have hnat : (185021841 : ℕ)^33*100000000000000^25 ≤ 8031804707821^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185021841 1250000000 8031804707821 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165611207/5000000000 : ℝ)^33 ≤ (1113161116783/100000000000000 : ℝ)^25 := by
    have hnat : (165611207 : ℕ)^33*100000000000000^25 ≤ 1113161116783^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165611207 5000000000 1113161116783 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9299213293/10000000000 : ℝ), (185021841/1250000000 : ℝ), (-165611207/5000000000 : ℝ)] ![(45427517079983/50000000000000 : ℝ), (8031804707821/100000000000000 : ℝ), (1113161116783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9299213293/10000000000 : ℝ)|^33 ≤ (45427517079983/50000000000000 : ℝ)^25
        have hw : |(9299213293/10000000000 : ℝ)|=(9299213293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(185021841/1250000000 : ℝ)|^33 ≤ (8031804707821/100000000000000 : ℝ)^25
        have hw : |(185021841/1250000000 : ℝ)|=(185021841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165611207/5000000000 : ℝ)|^33 ≤ (1113161116783/100000000000000 : ℝ)^25
        have hw : |(-165611207/5000000000 : ℝ)|=(165611207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (518312067/1000000000 : ℝ)*x 0 + (-856701491/2000000000 : ℝ)*x 1 + (706958707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518312067/1000000000 : ℝ)^33 ≤ (21000544084173/50000000000000 : ℝ)^25 := by
    have hnat : (518312067 : ℕ)^33*50000000000000^25 ≤ 21000544084173^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518312067 1000000000 21000544084173 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856701491/2000000000 : ℝ)^33 ≤ (3265693153517/10000000000000 : ℝ)^25 := by
    have hnat : (856701491 : ℕ)^33*10000000000000^25 ≤ 3265693153517^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856701491 2000000000 3265693153517 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706958707/2000000000 : ℝ)^33 ≤ (5068396056311/20000000000000 : ℝ)^25 := by
    have hnat : (706958707 : ℕ)^33*20000000000000^25 ≤ 5068396056311^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706958707 2000000000 5068396056311 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518312067/1000000000 : ℝ), (-856701491/2000000000 : ℝ), (706958707/2000000000 : ℝ)] ![(21000544084173/50000000000000 : ℝ), (3265693153517/10000000000000 : ℝ), (5068396056311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518312067/1000000000 : ℝ)|^33 ≤ (21000544084173/50000000000000 : ℝ)^25
        have hw : |(518312067/1000000000 : ℝ)|=(518312067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-856701491/2000000000 : ℝ)|^33 ≤ (3265693153517/10000000000000 : ℝ)^25
        have hw : |(-856701491/2000000000 : ℝ)|=(856701491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706958707/2000000000 : ℝ)|^33 ≤ (5068396056311/20000000000000 : ℝ)^25
        have hw : |(706958707/2000000000 : ℝ)|=(706958707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (523968667/2000000000 : ℝ)*x 0 + (-1218016111/5000000000 : ℝ)*x 1 + (-7419057851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523968667/2000000000 : ℝ)^33 ≤ (8532836592601/50000000000000 : ℝ)^25 := by
    have hnat : (523968667 : ℕ)^33*50000000000000^25 ≤ 8532836592601^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523968667 2000000000 8532836592601 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1218016111/5000000000 : ℝ)^33 ≤ (15503208850571/100000000000000 : ℝ)^25 := by
    have hnat : (1218016111 : ℕ)^33*100000000000000^25 ≤ 15503208850571^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218016111 5000000000 15503208850571 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7419057851/10000000000 : ℝ)^33 ≤ (33715558975829/50000000000000 : ℝ)^25 := by
    have hnat : (7419057851 : ℕ)^33*50000000000000^25 ≤ 33715558975829^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7419057851 10000000000 33715558975829 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523968667/2000000000 : ℝ), (-1218016111/5000000000 : ℝ), (-7419057851/10000000000 : ℝ)] ![(8532836592601/50000000000000 : ℝ), (15503208850571/100000000000000 : ℝ), (33715558975829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523968667/2000000000 : ℝ)|^33 ≤ (8532836592601/50000000000000 : ℝ)^25
        have hw : |(523968667/2000000000 : ℝ)|=(523968667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1218016111/5000000000 : ℝ)|^33 ≤ (15503208850571/100000000000000 : ℝ)^25
        have hw : |(-1218016111/5000000000 : ℝ)|=(1218016111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7419057851/10000000000 : ℝ)|^33 ≤ (33715558975829/50000000000000 : ℝ)^25
        have hw : |(-7419057851/10000000000 : ℝ)|=(7419057851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-118389833/10000000000 : ℝ)*x 0 + (-6672469281/10000000000 : ℝ)*x 1 + (-2548955513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118389833/10000000000 : ℝ)^33 ≤ (8945920619/3125000000000 : ℝ)^25 := by
    have hnat : (118389833 : ℕ)^33*3125000000000^25 ≤ 8945920619^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118389833 10000000000 8945920619 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6672469281/10000000000 : ℝ)^33 ≤ (58621683937973/100000000000000 : ℝ)^25 := by
    have hnat : (6672469281 : ℕ)^33*100000000000000^25 ≤ 58621683937973^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6672469281 10000000000 58621683937973 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548955513/5000000000 : ℝ)^33 ≤ (41092046595931/100000000000000 : ℝ)^25 := by
    have hnat : (2548955513 : ℕ)^33*100000000000000^25 ≤ 41092046595931^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548955513 5000000000 41092046595931 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118389833/10000000000 : ℝ), (-6672469281/10000000000 : ℝ), (-2548955513/5000000000 : ℝ)] ![(8945920619/3125000000000 : ℝ), (58621683937973/100000000000000 : ℝ), (41092046595931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118389833/10000000000 : ℝ)|^33 ≤ (8945920619/3125000000000 : ℝ)^25
        have hw : |(-118389833/10000000000 : ℝ)|=(118389833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6672469281/10000000000 : ℝ)|^33 ≤ (58621683937973/100000000000000 : ℝ)^25
        have hw : |(-6672469281/10000000000 : ℝ)|=(6672469281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2548955513/5000000000 : ℝ)|^33 ≤ (41092046595931/100000000000000 : ℝ)^25
        have hw : |(-2548955513/5000000000 : ℝ)|=(2548955513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1146498683/1250000000 : ℝ)*x 0 + (1730590151/10000000000 : ℝ)*x 1 + (-284296527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146498683/1250000000 : ℝ)^33 ≤ (35687150601/40000000000 : ℝ)^25 := by
    have hnat : (1146498683 : ℕ)^33*40000000000^25 ≤ 35687150601^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146498683 1250000000 35687150601 40000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730590151/10000000000 : ℝ)^33 ≤ (4936127681877/50000000000000 : ℝ)^25 := by
    have hnat : (1730590151 : ℕ)^33*50000000000000^25 ≤ 4936127681877^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730590151 10000000000 4936127681877 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284296527/10000000000 : ℝ)^33 ≤ (454934063403/50000000000000 : ℝ)^25 := by
    have hnat : (284296527 : ℕ)^33*50000000000000^25 ≤ 454934063403^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284296527 10000000000 454934063403 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1146498683/1250000000 : ℝ), (1730590151/10000000000 : ℝ), (-284296527/10000000000 : ℝ)] ![(35687150601/40000000000 : ℝ), (4936127681877/50000000000000 : ℝ), (454934063403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1146498683/1250000000 : ℝ)|^33 ≤ (35687150601/40000000000 : ℝ)^25
        have hw : |(1146498683/1250000000 : ℝ)|=(1146498683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1730590151/10000000000 : ℝ)|^33 ≤ (4936127681877/50000000000000 : ℝ)^25
        have hw : |(1730590151/10000000000 : ℝ)|=(1730590151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284296527/10000000000 : ℝ)|^33 ≤ (454934063403/50000000000000 : ℝ)^25
        have hw : |(-284296527/10000000000 : ℝ)|=(284296527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3595712331/10000000000 : ℝ)*x 0 + (-4835306057/10000000000 : ℝ)*x 1 + (286769331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3595712331/10000000000 : ℝ)^33 ≤ (3240008376999/12500000000000 : ℝ)^25 := by
    have hnat : (3595712331 : ℕ)^33*12500000000000^25 ≤ 3240008376999^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3595712331 10000000000 3240008376999 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4835306057/10000000000 : ℝ)^33 ≤ (9580311872907/25000000000000 : ℝ)^25 := by
    have hnat : (4835306057 : ℕ)^33*25000000000000^25 ≤ 9580311872907^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835306057 10000000000 9580311872907 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286769331/625000000 : ℝ)^33 ≤ (893967136813/2500000000000 : ℝ)^25 := by
    have hnat : (286769331 : ℕ)^33*2500000000000^25 ≤ 893967136813^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286769331 625000000 893967136813 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3595712331/10000000000 : ℝ), (-4835306057/10000000000 : ℝ), (286769331/625000000 : ℝ)] ![(3240008376999/12500000000000 : ℝ), (9580311872907/25000000000000 : ℝ), (893967136813/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3595712331/10000000000 : ℝ)|^33 ≤ (3240008376999/12500000000000 : ℝ)^25
        have hw : |(3595712331/10000000000 : ℝ)|=(3595712331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4835306057/10000000000 : ℝ)|^33 ≤ (9580311872907/25000000000000 : ℝ)^25
        have hw : |(-4835306057/10000000000 : ℝ)|=(4835306057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286769331/625000000 : ℝ)|^33 ≤ (893967136813/2500000000000 : ℝ)^25
        have hw : |(286769331/625000000 : ℝ)|=(286769331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s0_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4873872337/10000000000 : ℝ)*x 0 + (-2974881757/10000000000 : ℝ)*x 1 + (-2548955513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4873872337/10000000000 : ℝ)^33 ≤ (7745043705497/20000000000000 : ℝ)^25 := by
    have hnat : (4873872337 : ℕ)^33*20000000000000^25 ≤ 7745043705497^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873872337 10000000000 7745043705497 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2974881757/10000000000 : ℝ)^33 ≤ (20182734870409/100000000000000 : ℝ)^25 := by
    have hnat : (2974881757 : ℕ)^33*100000000000000^25 ≤ 20182734870409^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974881757 10000000000 20182734870409 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548955513/5000000000 : ℝ)^33 ≤ (41092046595931/100000000000000 : ℝ)^25 := by
    have hnat : (2548955513 : ℕ)^33*100000000000000^25 ≤ 41092046595931^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548955513 5000000000 41092046595931 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4873872337/10000000000 : ℝ), (-2974881757/10000000000 : ℝ), (-2548955513/5000000000 : ℝ)] ![(7745043705497/20000000000000 : ℝ), (20182734870409/100000000000000 : ℝ), (41092046595931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4873872337/10000000000 : ℝ)|^33 ≤ (7745043705497/20000000000000 : ℝ)^25
        have hw : |(4873872337/10000000000 : ℝ)|=(4873872337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2974881757/10000000000 : ℝ)|^33 ≤ (20182734870409/100000000000000 : ℝ)^25
        have hw : |(-2974881757/10000000000 : ℝ)|=(2974881757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2548955513/5000000000 : ℝ)|^33 ≤ (41092046595931/100000000000000 : ℝ)^25
        have hw : |(-2548955513/5000000000 : ℝ)|=(2548955513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-280118883/1250000000 : ℝ)*x 0 + (-4918211059/10000000000 : ℝ)*x 1 + (-5637049279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280118883/1250000000 : ℝ)^33 ≤ (3471448612923/25000000000000 : ℝ)^25 := by
    have hnat : (280118883 : ℕ)^33*25000000000000^25 ≤ 3471448612923^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280118883 1250000000 3471448612923 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918211059/10000000000 : ℝ)^33 ≤ (9797729893493/25000000000000 : ℝ)^25 := by
    have hnat : (4918211059 : ℕ)^33*25000000000000^25 ≤ 9797729893493^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918211059 10000000000 9797729893493 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637049279/10000000000 : ℝ)^33 ≤ (11730821491603/25000000000000 : ℝ)^25 := by
    have hnat : (5637049279 : ℕ)^33*25000000000000^25 ≤ 11730821491603^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637049279 10000000000 11730821491603 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280118883/1250000000 : ℝ), (-4918211059/10000000000 : ℝ), (-5637049279/10000000000 : ℝ)] ![(3471448612923/25000000000000 : ℝ), (9797729893493/25000000000000 : ℝ), (11730821491603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280118883/1250000000 : ℝ)|^33 ≤ (3471448612923/25000000000000 : ℝ)^25
        have hw : |(-280118883/1250000000 : ℝ)|=(280118883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4918211059/10000000000 : ℝ)|^33 ≤ (9797729893493/25000000000000 : ℝ)^25
        have hw : |(-4918211059/10000000000 : ℝ)|=(4918211059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5637049279/10000000000 : ℝ)|^33 ≤ (11730821491603/25000000000000 : ℝ)^25
        have hw : |(-5637049279/10000000000 : ℝ)|=(5637049279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (810538773/1250000000 : ℝ)*x 0 + (1682083003/5000000000 : ℝ)*x 1 + (-73330919/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810538773/1250000000 : ℝ)^33 ≤ (56449511985823/100000000000000 : ℝ)^25 := by
    have hnat : (810538773 : ℕ)^33*100000000000000^25 ≤ 56449511985823^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810538773 1250000000 56449511985823 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1682083003/5000000000 : ℝ)^33 ≤ (1186993104891/5000000000000 : ℝ)^25 := by
    have hnat : (1682083003 : ℕ)^33*5000000000000^25 ≤ 1186993104891^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682083003 5000000000 1186993104891 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73330919/250000000 : ℝ)^33 ≤ (247632823867/1250000000000 : ℝ)^25 := by
    have hnat : (73330919 : ℕ)^33*1250000000000^25 ≤ 247632823867^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73330919 250000000 247632823867 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(810538773/1250000000 : ℝ), (1682083003/5000000000 : ℝ), (-73330919/250000000 : ℝ)] ![(56449511985823/100000000000000 : ℝ), (1186993104891/5000000000000 : ℝ), (247632823867/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(810538773/1250000000 : ℝ)|^33 ≤ (56449511985823/100000000000000 : ℝ)^25
        have hw : |(810538773/1250000000 : ℝ)|=(810538773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1682083003/5000000000 : ℝ)|^33 ≤ (1186993104891/5000000000000 : ℝ)^25
        have hw : |(1682083003/5000000000 : ℝ)|=(1682083003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73330919/250000000 : ℝ)|^33 ≤ (247632823867/1250000000000 : ℝ)^25
        have hw : |(-73330919/250000000 : ℝ)|=(73330919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4330452737/10000000000 : ℝ)*x 0 + (-931099483/2000000000 : ℝ)*x 1 + (4059156453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330452737/10000000000 : ℝ)^33 ≤ (33130192551803/100000000000000 : ℝ)^25 := by
    have hnat : (4330452737 : ℕ)^33*100000000000000^25 ≤ 33130192551803^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330452737 10000000000 33130192551803 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931099483/2000000000 : ℝ)^33 ≤ (36451486075611/100000000000000 : ℝ)^25 := by
    have hnat : (931099483 : ℕ)^33*100000000000000^25 ≤ 36451486075611^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931099483 2000000000 36451486075611 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4059156453/10000000000 : ℝ)^33 ≤ (30418321361801/100000000000000 : ℝ)^25 := by
    have hnat : (4059156453 : ℕ)^33*100000000000000^25 ≤ 30418321361801^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059156453 10000000000 30418321361801 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330452737/10000000000 : ℝ), (-931099483/2000000000 : ℝ), (4059156453/10000000000 : ℝ)] ![(33130192551803/100000000000000 : ℝ), (36451486075611/100000000000000 : ℝ), (30418321361801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330452737/10000000000 : ℝ)|^33 ≤ (33130192551803/100000000000000 : ℝ)^25
        have hw : |(4330452737/10000000000 : ℝ)|=(4330452737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-931099483/2000000000 : ℝ)|^33 ≤ (36451486075611/100000000000000 : ℝ)^25
        have hw : |(-931099483/2000000000 : ℝ)|=(931099483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4059156453/10000000000 : ℝ)|^33 ≤ (30418321361801/100000000000000 : ℝ)^25
        have hw : |(4059156453/10000000000 : ℝ)|=(4059156453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303068_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1991619903/5000000000 : ℝ)*x 0 + (-4218830647/10000000000 : ℝ)*x 1 + (-2417724247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991619903/5000000000 : ℝ)^33 ≤ (29669629181543/100000000000000 : ℝ)^25 := by
    have hnat : (1991619903 : ℕ)^33*100000000000000^25 ≤ 29669629181543^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991619903 5000000000 29669629181543 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218830647/10000000000 : ℝ)^33 ≤ (32007633217089/100000000000000 : ℝ)^25 := by
    have hnat : (4218830647 : ℕ)^33*100000000000000^25 ≤ 32007633217089^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218830647 10000000000 32007633217089 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417724247/5000000000 : ℝ)^33 ≤ (38322737588373/100000000000000 : ℝ)^25 := by
    have hnat : (2417724247 : ℕ)^33*100000000000000^25 ≤ 38322737588373^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417724247 5000000000 38322737588373 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1991619903/5000000000 : ℝ), (-4218830647/10000000000 : ℝ), (-2417724247/5000000000 : ℝ)] ![(29669629181543/100000000000000 : ℝ), (32007633217089/100000000000000 : ℝ), (38322737588373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1991619903/5000000000 : ℝ)|^33 ≤ (29669629181543/100000000000000 : ℝ)^25
        have hw : |(1991619903/5000000000 : ℝ)|=(1991619903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4218830647/10000000000 : ℝ)|^33 ≤ (32007633217089/100000000000000 : ℝ)^25
        have hw : |(-4218830647/10000000000 : ℝ)|=(4218830647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2417724247/5000000000 : ℝ)|^33 ≤ (38322737588373/100000000000000 : ℝ)^25
        have hw : |(-2417724247/5000000000 : ℝ)|=(2417724247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303068 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
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
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((7717852567/10000000000 : ℝ)*X 1 0+(751169169/2500000000 : ℝ)*X 1 1+(-1546639757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-24878067/625000000 : ℝ)*X 0 0+(-5779651781/10000000000 : ℝ)*X 0 1+(-5922486613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7661563867/10000000000 : ℝ)*X 1 0+(3692252339/10000000000 : ℝ)*X 1 1+(-666514267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((460545821/1000000000 : ℝ)*X 2 0+(-718410811/2500000000 : ℝ)*X 2 1+(544122943/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((540590967/1000000000 : ℝ)*X 0 0+(-111331423/1000000000 : ℝ)*X 0 1+(-5922486613/10000000000 : ℝ)*X 0 2+(540590967/1000000000 : ℝ)*X 1 0+(-111331423/1000000000 : ℝ)*X 1 1+(-5922486613/10000000000 : ℝ)*X 1 2+(540590967/1000000000 : ℝ)*X 2 0+(-111331423/1000000000 : ℝ)*X 2 1+(-5922486613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-136828353/10000000000 : ℝ)*X 0 0+(-1060063207/2500000000 : ℝ)*X 0 1+(-7419057851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((9299213293/10000000000 : ℝ)*X 1 0+(185021841/1250000000 : ℝ)*X 1 1+(-165611207/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((518312067/1000000000 : ℝ)*X 2 0+(-856701491/2000000000 : ℝ)*X 2 1+(706958707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((523968667/2000000000 : ℝ)*X 0 0+(-1218016111/5000000000 : ℝ)*X 0 1+(-7419057851/10000000000 : ℝ)*X 0 2+(523968667/2000000000 : ℝ)*X 1 0+(-1218016111/5000000000 : ℝ)*X 1 1+(-7419057851/10000000000 : ℝ)*X 1 2+(523968667/2000000000 : ℝ)*X 2 0+(-1218016111/5000000000 : ℝ)*X 2 1+(-7419057851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-118389833/10000000000 : ℝ)*X 0 0+(-6672469281/10000000000 : ℝ)*X 0 1+(-2548955513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1146498683/1250000000 : ℝ)*X 1 0+(1730590151/10000000000 : ℝ)*X 1 1+(-284296527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3595712331/10000000000 : ℝ)*X 2 0+(-4835306057/10000000000 : ℝ)*X 2 1+(286769331/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4873872337/10000000000 : ℝ)*X 0 0+(-2974881757/10000000000 : ℝ)*X 0 1+(-2548955513/5000000000 : ℝ)*X 0 2+(4873872337/10000000000 : ℝ)*X 1 0+(-2974881757/10000000000 : ℝ)*X 1 1+(-2548955513/5000000000 : ℝ)*X 1 2+(4873872337/10000000000 : ℝ)*X 2 0+(-2974881757/10000000000 : ℝ)*X 2 1+(-2548955513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14593/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14593/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50219932004387492679573/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1403030497459/1000000000000 : ℝ)*(base1) + (1759995175083/1000000000000 : ℝ)*(base39) + (236370544733/1000000000000 : ℝ)*(base49) + (3141833/1000000000000 : ℝ)*(base54) + (2358296978553/1000000000000 : ℝ)*(major_s0_0) + (2358296978553/1000000000000 : ℝ)*(major_s0_1) + (2358293836721/1000000000000 : ℝ)*(major_s0_2) + (9734179/250000000000 : ℝ)*(sp_s0_1) + (4551809955669/1000000000000 : ℝ)*(sp_s0_7) + (314874354943/100000000000 : ℝ)*(sp_s0_8) + (787186779109/250000000000 : ℝ)*(sp_s0_9) + (82387241833/500000000000 : ℝ)*(sp_s0_13) + (94623/31250000000 : ℝ)*(sp_s0_14) + (32227877/1000000000000 : ℝ)*(sp_s0_23) + (783904061479/500000000000 : ℝ)*(f.failure) + (629756497229/200000000000 : ℝ)*(f.sum) + (3330658919080049/10000000000000000000000000000 : ℝ)*base63 + (572901975043351/1250000000000000000000000000 : ℝ)*base65 + (133233422861133/2000000000000000000000000000 : ℝ)*base66 + (1795019910144219/2000000000000000000000000000 : ℝ)*base68 + (3288121477347527/10000000000000000000000000000 : ℝ)*base70 + (812025628975143/1250000000000000000000000000 : ℝ)*base72 + (420467119399857/1250000000000000000000000000 : ℝ)*base74 + (916578311661133/2000000000000000000000000000 : ℝ)*base77 + (4280311931106809/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1059/2500000000000000 : ℝ)*base87 + (1059/2500000000000000 : ℝ)*base89 + (1441/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-68607/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-68607/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3299373891999182852991/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1696835509553/1000000000000 : ℝ)*(base1) + (1067089/100000000000 : ℝ)*(base33) + (2392248277619/1000000000000 : ℝ)*(base39) + (47948777843/100000000000 : ℝ)*(base49) + (32820721141/100000000000 : ℝ)*(base60) + (3340969317813/1000000000000 : ℝ)*(major_s0_0) + (1670489994351/500000000000 : ℝ)*(major_s0_1) + (1670489994351/500000000000 : ℝ)*(major_s0_2) + (462217/8000000000 : ℝ)*(sp_s0_9) + (1231538035573/200000000000 : ℝ)*(sp_s0_14) + (4460430428459/1000000000000 : ℝ)*(sp_s0_15) + (4460786220297/1000000000000 : ℝ)*(sp_s0_16) + (524265400367/1000000000000 : ℝ)*(sp_s0_20) + (103392241/250000000000 : ℝ)*(sp_s0_22) + (13881880687/6250000000 : ℝ)*(f.failure) + (557606833539/125000000000 : ℝ)*(f.sum) + (618166278634897/5000000000000000000000000000 : ℝ)*base62 + (6523698420119/625000000000000000000000000 : ℝ)*base64 + (181787752054789/1000000000000000000000000000 : ℝ)*base67 + (710878281654789/1000000000000000000000000000 : ℝ)*base68 + (2782026513201939/10000000000000000000000000000 : ℝ)*base70 + (761392996082797/1250000000000000000000000000 : ℝ)*base73 + (402284621642381/625000000000000000000000000 : ℝ)*base75 + (484299141303993/2000000000000000000000000000 : ℝ)*base77 + (1654042679105133/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (167/125000000000000 : ℝ)*base86 + (21/62500000000000 : ℝ)*base88 + (21/62500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-51781/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-51781/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28686978838815428365623/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147109608279/500000000000 : ℝ)*(base1) + (1126583/250000000000 : ℝ)*(base10) + (150185354789/125000000000 : ℝ)*(base39) + (35557/15625000000 : ℝ)*(base43) + (185611760713/500000000000 : ℝ)*(base49) + (1569917684511/500000000000 : ℝ)*(major_s0_0) + (25118664747/8000000000 : ℝ)*(major_s0_1) + (1569917684511/500000000000 : ℝ)*(major_s0_2) + (513449/100000000000 : ℝ)*(sp_s0_8) + (17774561/1000000000000 : ℝ)*(sp_s0_16) + (280406396361/62500000000 : ℝ)*(sp_s0_21) + (4192284772707/1000000000000 : ℝ)*(sp_s0_22) + (4192269856989/1000000000000 : ℝ)*(sp_s0_23) + (1793159701819/1000000000000 : ℝ)*(sp_s0_27) + (2087378918377/1000000000000 : ℝ)*(f.failure) + (4192289907197/1000000000000 : ℝ)*(f.sum) + (59844622971329/1000000000000000000000000000 : ℝ)*base62 + (181019695162659/625000000000000000000000000 : ℝ)*base64 + (8383073031833/16000000000000000000000000 : ℝ)*base67 + (129931648287029/1000000000000000000000000000 : ℝ)*base68 + (1126208676263583/5000000000000000000000000000 : ℝ)*base71 + (318607992162659/625000000000000000000000000 : ℝ)*base73 + (3832713264843/10000000000000000000000000 : ℝ)*base74 + (231725299087029/1000000000000000000000000000 : ℝ)*base76 + (741179751498169/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (3417/5000000000000000 : ℝ)*base87 + (1583/5000000000000000 : ℝ)*base88 + (3417/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (14593/50000 : ℝ) ^ (131/32 : ℝ) ≤ (161621241282573401/25000000000000000000 : ℝ) := by
    have hpowers : (14593/50000 : ℝ)^131 ≤ (161621241282573401/25000000000000000000 : ℝ)^32 := by
      have hnat : (14593 : ℕ)^131*25000000000000000000^32 ≤ 161621241282573401^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14593 50000 161621241282573401 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14593/50000 : ℝ)) (X := (161621241282573401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25161621241282573401/25000000000000000000 : ℝ) ≤ (10015753567369463/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25161621241282573401/25000000000000000000 : ℝ)^32 ≤ (10015753567369463/10000000000000000 : ℝ)^131 := by
      have hnat : (25161621241282573401 : ℕ)^32*10000000000000000^131 ≤ 10015753567369463^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25161621241282573401 25000000000000000000 10015753567369463 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015753567369463/10000000000000000 : ℝ)) (X := (25161621241282573401/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12661621241282573401/12500000000000000000 : ℝ) ≤ (5015715423646833/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (12661621241282573401/12500000000000000000 : ℝ)^32 ≤ (5015715423646833/5000000000000000 : ℝ)^131 := by
      have hnat : (12661621241282573401 : ℕ)^32*5000000000000000^131 ≤ 5015715423646833^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12661621241282573401 12500000000000000000 5015715423646833 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015715423646833/5000000000000000 : ℝ)) (X := (12661621241282573401/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(15753567369463/2918600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15677279924203/2918600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (14593/50000 : ℝ)) (alpha := (15753567369463/2918600000000000 : ℝ)) (beta := (15677279924203/2918600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14593/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(15753567369463/2918600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15677279924203/2918600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (68607/100000 : ℝ) ^ (131/32 : ℝ) ≤ (1069309096684891063/5000000000000000000 : ℝ) := by
    have hpowers : (68607/100000 : ℝ)^131 ≤ (1069309096684891063/5000000000000000000 : ℝ)^32 := by
      have hnat : (68607 : ℕ)^131*5000000000000000000^32 ≤ 1069309096684891063^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68607 100000 1069309096684891063 5000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68607/100000 : ℝ)) (X := (1069309096684891063/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (6069309096684891063/5000000000000000000 : ℝ) ≤ (10484806692402067/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6069309096684891063/5000000000000000000 : ℝ)^32 ≤ (10484806692402067/10000000000000000 : ℝ)^131 := by
      have hnat : (6069309096684891063 : ℕ)^32*10000000000000000^131 ≤ 10484806692402067^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6069309096684891063 5000000000000000000 10484806692402067 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10484806692402067/10000000000000000 : ℝ)) (X := (6069309096684891063/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3569309096684891063/2500000000000000000 : ℝ) ≤ (136359588911021/125000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3569309096684891063/2500000000000000000 : ℝ)^32 ≤ (136359588911021/125000000000000 : ℝ)^131 := by
      have hnat : (3569309096684891063 : ℕ)^32*125000000000000^131 ≤ 136359588911021^131*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3569309096684891063 2500000000000000000 136359588911021 125000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (136359588911021/125000000000000 : ℝ)) (X := (3569309096684891063/2500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(23086032971527/326700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(141320140159871/2286900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (68607/100000 : ℝ)) (alpha := (23086032971527/326700000000000 : ℝ)) (beta := (141320140159871/2286900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (68607/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(23086032971527/326700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(141320140159871/2286900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (51781/100000 : ℝ) ^ (131/32 : ℝ) ≤ (270361721266516453/4000000000000000000 : ℝ) := by
    have hpowers : (51781/100000 : ℝ)^131 ≤ (270361721266516453/4000000000000000000 : ℝ)^32 := by
      have hnat : (51781 : ℕ)^131*4000000000000000000^32 ≤ 270361721266516453^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51781 100000 270361721266516453 4000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51781/100000 : ℝ)) (X := (270361721266516453/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4270361721266516453/4000000000000000000 : ℝ) ≤ (1270131125575277/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (4270361721266516453/4000000000000000000 : ℝ)^32 ≤ (1270131125575277/1250000000000000 : ℝ)^131 := by
      have hnat : (4270361721266516453 : ℕ)^32*1250000000000000^131 ≤ 1270131125575277^131*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4270361721266516453 4000000000000000000 1270131125575277 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1270131125575277/1250000000000000 : ℝ)) (X := (4270361721266516453/4000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2270361721266516453/2000000000000000000 : ℝ) ≤ (2578641784647689/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2270361721266516453/2000000000000000000 : ℝ)^32 ≤ (2578641784647689/2500000000000000 : ℝ)^131 := by
      have hnat : (2270361721266516453 : ℕ)^32*2500000000000000^131 ≤ 2578641784647689^131*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2270361721266516453 2000000000000000000 2578641784647689 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2578641784647689/2500000000000000 : ℝ)) (X := (2270361721266516453/2000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(20131125575277/647262500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7675906699427/258905000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (51781/100000 : ℝ)) (alpha := (20131125575277/647262500000000 : ℝ)) (beta := (7675906699427/258905000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (51781/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(20131125575277/647262500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7675906699427/258905000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-280118883/1250000000 : ℝ)*X 0 0+(-4918211059/10000000000 : ℝ)*X 0 1+(-5637049279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((810538773/1250000000 : ℝ)*X 1 0+(1682083003/5000000000 : ℝ)*X 1 1+(-73330919/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4330452737/10000000000 : ℝ)*X 2 0+(-931099483/2000000000 : ℝ)*X 2 1+(4059156453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1991619903/5000000000 : ℝ)*X 0 0+(-4218830647/10000000000 : ℝ)*X 0 1+(-2417724247/5000000000 : ℝ)*X 0 2+(1991619903/5000000000 : ℝ)*X 1 0+(-4218830647/10000000000 : ℝ)*X 1 1+(-2417724247/5000000000 : ℝ)*X 1 2+(1991619903/5000000000 : ℝ)*X 2 0+(-4218830647/10000000000 : ℝ)*X 2 1+(-2417724247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-45319875084031046965029462321627/7556401330000000000000000000000 : ℝ) := by norm_num
    linear_combination (277963/500000000000 : ℝ)*(base3) + (565443/1000000000000 : ℝ)*(base10) + (11277/40000000000 : ℝ)*(base21) + (218927/500000000000 : ℝ)*(base33) + (284823753689/500000000000 : ℝ)*(base39) + (71739745063/500000000000 : ℝ)*(base40) + (147186517093/1000000000000 : ℝ)*(base49) + (71836321053/500000000000 : ℝ)*(base60) + (752099781073/500000000000 : ℝ)*(major_s1_0) + (7521/5000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (1999181898307/1000000000000 : ℝ)*(sp_s1_0) + (999591290911/500000000000 : ℝ)*(sp_s1_1) + (1999181743971/1000000000000 : ℝ)*(sp_s1_2) + (499999722037/500000000000 : ℝ)*(sp_s1_6) + (1599345971/800000000 : ℝ)*(f.sum) + (230235580653565813/986816407500000000000000000000 : ℝ)*base63 + (307326337186971/517810000000000000000000000 : ℝ)*base65 + (786613417399/10890000000000000000000000 : ℝ)*base66 + (5500019201837/129452500000000000000000000 : ℝ)*base69 + (8235328083264095801/75564013300000000000000000000000 : ℝ)*base70 + (387752611216499/1459300000000000000000000000 : ℝ)*base73 + (42604072449833/76230000000000000000000000 : ℝ)*base74 + (511072376307211/1459300000000000000000000000 : ℝ)*base76 + (74996569222037501/1589177700000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b028 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 := by omega
  rcases hc with rfl
  · exact collision_c303068 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b028 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
