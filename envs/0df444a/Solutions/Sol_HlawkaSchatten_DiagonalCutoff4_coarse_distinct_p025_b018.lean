-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:15.460521+00:00
-- url     : https://prove2.me/submissions/b33dd6af-705f-42af-bb09-f417b034f88a

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
theorem collision_support_c325038_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-704426663/10000000000 : ℝ)*x 0 + (-2236715961/5000000000 : ℝ)*x 1 + (-3241980523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704426663/10000000000 : ℝ)^87 ≤ (242143694011/6250000000000 : ℝ)^71 := by
    have hnat : (704426663 : ℕ)^87*6250000000000^71 ≤ 242143694011^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704426663 10000000000 242143694011 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236715961/5000000000 : ℝ)^87 ≤ (37317453989863/100000000000000 : ℝ)^71 := by
    have hnat : (2236715961 : ℕ)^87*100000000000000^71 ≤ 37317453989863^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236715961 5000000000 37317453989863 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3241980523/5000000000 : ℝ)^87 ≤ (7351030861231/12500000000000 : ℝ)^71 := by
    have hnat : (3241980523 : ℕ)^87*12500000000000^71 ≤ 7351030861231^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241980523 5000000000 7351030861231 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704426663/10000000000 : ℝ), (-2236715961/5000000000 : ℝ), (-3241980523/5000000000 : ℝ)] ![(242143694011/6250000000000 : ℝ), (37317453989863/100000000000000 : ℝ), (7351030861231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704426663/10000000000 : ℝ)|^87 ≤ (242143694011/6250000000000 : ℝ)^71
        have hw : |(-704426663/10000000000 : ℝ)|=(704426663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236715961/5000000000 : ℝ)|^87 ≤ (37317453989863/100000000000000 : ℝ)^71
        have hw : |(-2236715961/5000000000 : ℝ)|=(2236715961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3241980523/5000000000 : ℝ)|^87 ≤ (7351030861231/12500000000000 : ℝ)^71
        have hw : |(-3241980523/5000000000 : ℝ)|=(3241980523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5014690489/10000000000 : ℝ)*x 0 + (-165830223/400000000 : ℝ)*x 1 + (3022383119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5014690489/10000000000 : ℝ)^87 ≤ (21461670338391/50000000000000 : ℝ)^71 := by
    have hnat : (5014690489 : ℕ)^87*50000000000000^71 ≤ 21461670338391^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014690489 10000000000 21461670338391 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165830223/400000000 : ℝ)^87 ≤ (33996161042531/100000000000000 : ℝ)^71 := by
    have hnat : (165830223 : ℕ)^87*100000000000000^71 ≤ 33996161042531^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165830223 400000000 33996161042531 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3022383119/10000000000 : ℝ)^87 ≤ (23080498267359/100000000000000 : ℝ)^71 := by
    have hnat : (3022383119 : ℕ)^87*100000000000000^71 ≤ 23080498267359^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022383119 10000000000 23080498267359 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5014690489/10000000000 : ℝ), (-165830223/400000000 : ℝ), (3022383119/10000000000 : ℝ)] ![(21461670338391/50000000000000 : ℝ), (33996161042531/100000000000000 : ℝ), (23080498267359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5014690489/10000000000 : ℝ)|^87 ≤ (21461670338391/50000000000000 : ℝ)^71
        have hw : |(5014690489/10000000000 : ℝ)|=(5014690489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165830223/400000000 : ℝ)|^87 ≤ (33996161042531/100000000000000 : ℝ)^71
        have hw : |(-165830223/400000000 : ℝ)|=(165830223/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3022383119/10000000000 : ℝ)|^87 ≤ (23080498267359/100000000000000 : ℝ)^71
        have hw : |(3022383119/10000000000 : ℝ)|=(3022383119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7730981719/10000000000 : ℝ)*x 0 + (-397311817/2500000000 : ℝ)*x 1 + (-460702993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7730981719/10000000000 : ℝ)^87 ≤ (2279807139783/3125000000000 : ℝ)^71 := by
    have hnat : (7730981719 : ℕ)^87*3125000000000^71 ≤ 2279807139783^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7730981719 10000000000 2279807139783 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397311817/2500000000 : ℝ)^87 ≤ (5249866850833/50000000000000 : ℝ)^71 := by
    have hnat : (397311817 : ℕ)^87*50000000000000^71 ≤ 5249866850833^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397311817 2500000000 5249866850833 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460702993/2000000000 : ℝ)^87 ≤ (4136609452939/25000000000000 : ℝ)^71 := by
    have hnat : (460702993 : ℕ)^87*25000000000000^71 ≤ 4136609452939^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460702993 2000000000 4136609452939 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7730981719/10000000000 : ℝ), (-397311817/2500000000 : ℝ), (-460702993/2000000000 : ℝ)] ![(2279807139783/3125000000000 : ℝ), (5249866850833/50000000000000 : ℝ), (4136609452939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7730981719/10000000000 : ℝ)|^87 ≤ (2279807139783/3125000000000 : ℝ)^71
        have hw : |(7730981719/10000000000 : ℝ)|=(7730981719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397311817/2500000000 : ℝ)|^87 ≤ (5249866850833/50000000000000 : ℝ)^71
        have hw : |(-397311817/2500000000 : ℝ)|=(397311817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460702993/2000000000 : ℝ)|^87 ≤ (4136609452939/25000000000000 : ℝ)^71
        have hw : |(-460702993/2000000000 : ℝ)|=(460702993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-340364509/5000000000 : ℝ)*x 0 + (-4561707261/10000000000 : ℝ)*x 1 + (-100262911/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340364509/5000000000 : ℝ)^87 ≤ (3715203001143/100000000000000 : ℝ)^71 := by
    have hnat : (340364509 : ℕ)^87*100000000000000^71 ≤ 3715203001143^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340364509 5000000000 3715203001143 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561707261/10000000000 : ℝ)^87 ≤ (1911089640181/5000000000000 : ℝ)^71 := by
    have hnat : (4561707261 : ℕ)^87*5000000000000^71 ≤ 1911089640181^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561707261 10000000000 1911089640181 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100262911/156250000 : ℝ)^87 ≤ (58063004176181/100000000000000 : ℝ)^71 := by
    have hnat : (100262911 : ℕ)^87*100000000000000^71 ≤ 58063004176181^71*156250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100262911 156250000 58063004176181 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340364509/5000000000 : ℝ), (-4561707261/10000000000 : ℝ), (-100262911/156250000 : ℝ)] ![(3715203001143/100000000000000 : ℝ), (1911089640181/5000000000000 : ℝ), (58063004176181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340364509/5000000000 : ℝ)|^87 ≤ (3715203001143/100000000000000 : ℝ)^71
        have hw : |(-340364509/5000000000 : ℝ)|=(340364509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4561707261/10000000000 : ℝ)|^87 ≤ (1911089640181/5000000000000 : ℝ)^71
        have hw : |(-4561707261/10000000000 : ℝ)|=(4561707261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100262911/156250000 : ℝ)|^87 ≤ (58063004176181/100000000000000 : ℝ)^71
        have hw : |(-100262911/156250000 : ℝ)|=(100262911/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (626959893/1250000000 : ℝ)*x 0 + (4329007377/10000000000 : ℝ)*x 1 + (-564400709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (626959893/1250000000 : ℝ)^87 ≤ (42933710341153/100000000000000 : ℝ)^71 := by
    have hnat : (626959893 : ℕ)^87*100000000000000^71 ≤ 42933710341153^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626959893 1250000000 42933710341153 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4329007377/10000000000 : ℝ)^87 ≤ (35846575007169/100000000000000 : ℝ)^71 := by
    have hnat : (4329007377 : ℕ)^87*100000000000000^71 ≤ 35846575007169^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329007377 10000000000 35846575007169 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564400709/2000000000 : ℝ)^87 ≤ (2121971463667/10000000000000 : ℝ)^71 := by
    have hnat : (564400709 : ℕ)^87*10000000000000^71 ≤ 2121971463667^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564400709 2000000000 2121971463667 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(626959893/1250000000 : ℝ), (4329007377/10000000000 : ℝ), (-564400709/2000000000 : ℝ)] ![(42933710341153/100000000000000 : ℝ), (35846575007169/100000000000000 : ℝ), (2121971463667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(626959893/1250000000 : ℝ)|^87 ≤ (42933710341153/100000000000000 : ℝ)^71
        have hw : |(626959893/1250000000 : ℝ)|=(626959893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4329007377/10000000000 : ℝ)|^87 ≤ (35846575007169/100000000000000 : ℝ)^71
        have hw : |(4329007377/10000000000 : ℝ)|=(4329007377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564400709/2000000000 : ℝ)|^87 ≤ (2121971463667/10000000000000 : ℝ)^71
        have hw : |(-564400709/2000000000 : ℝ)|=(564400709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5015679017/10000000000 : ℝ)*x 0 + (-1973081569/5000000000 : ℝ)*x 1 + (3232801703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5015679017/10000000000 : ℝ)^87 ≤ (5366713626133/12500000000000 : ℝ)^71 := by
    have hnat : (5015679017 : ℕ)^87*12500000000000^71 ≤ 5366713626133^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015679017 10000000000 5366713626133 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973081569/5000000000 : ℝ)^87 ≤ (8000409837111/25000000000000 : ℝ)^71 := by
    have hnat : (1973081569 : ℕ)^87*25000000000000^71 ≤ 8000409837111^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973081569 5000000000 8000409837111 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3232801703/10000000000 : ℝ)^87 ≤ (5012930324759/20000000000000 : ℝ)^71 := by
    have hnat : (3232801703 : ℕ)^87*20000000000000^71 ≤ 5012930324759^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232801703 10000000000 5012930324759 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5015679017/10000000000 : ℝ), (-1973081569/5000000000 : ℝ), (3232801703/10000000000 : ℝ)] ![(5366713626133/12500000000000 : ℝ), (8000409837111/25000000000000 : ℝ), (5012930324759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5015679017/10000000000 : ℝ)|^87 ≤ (5366713626133/12500000000000 : ℝ)^71
        have hw : |(5015679017/10000000000 : ℝ)|=(5015679017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973081569/5000000000 : ℝ)|^87 ≤ (8000409837111/25000000000000 : ℝ)^71
        have hw : |(-1973081569/5000000000 : ℝ)|=(1973081569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3232801703/10000000000 : ℝ)|^87 ≤ (5012930324759/20000000000000 : ℝ)^71
        have hw : |(3232801703/10000000000 : ℝ)|=(3232801703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_10 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1999999997/2000000000 : ℝ)*x 0 + (73/1000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999999997/2000000000 : ℝ)^87 ≤ (49999999908099/50000000000000 : ℝ)^71 := by
    have hnat : (1999999997 : ℕ)^87*50000000000000^71 ≤ 49999999908099^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999999997 2000000000 49999999908099 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73/1000000000 : ℝ)^87 ≤ (179911/100000000000000 : ℝ)^71 := by
    have hnat : (73 : ℕ)^87*100000000000000^71 ≤ 179911^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73 1000000000 179911 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^87 ≤ (0 : ℝ)^71 := by
    have hnat : (0 : ℕ)^87*1^71 ≤ 0^71*1^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999999997/2000000000 : ℝ), (73/1000000000 : ℝ), (0 : ℝ)] ![(49999999908099/50000000000000 : ℝ), (179911/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999999997/2000000000 : ℝ)|^87 ≤ (49999999908099/50000000000000 : ℝ)^71
        have hw : |(1999999997/2000000000 : ℝ)|=(1999999997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73/1000000000 : ℝ)|^87 ≤ (179911/100000000000000 : ℝ)^71
        have hw : |(73/1000000000 : ℝ)|=(73/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^87 ≤ (0 : ℝ)^71
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7655912167/10000000000 : ℝ)*x 0 + (-1436089849/10000000000 : ℝ)*x 1 + (-2538687741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7655912167/10000000000 : ℝ)^87 ≤ (14417348745569/20000000000000 : ℝ)^71 := by
    have hnat : (7655912167 : ℕ)^87*20000000000000^71 ≤ 14417348745569^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7655912167 10000000000 14417348745569 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1436089849/10000000000 : ℝ)^87 ≤ (4636825076259/50000000000000 : ℝ)^71 := by
    have hnat : (1436089849 : ℕ)^87*50000000000000^71 ≤ 4636825076259^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436089849 10000000000 4636825076259 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538687741/10000000000 : ℝ)^87 ≤ (4659901526599/25000000000000 : ℝ)^71 := by
    have hnat : (2538687741 : ℕ)^87*25000000000000^71 ≤ 4659901526599^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538687741 10000000000 4659901526599 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7655912167/10000000000 : ℝ), (-1436089849/10000000000 : ℝ), (-2538687741/10000000000 : ℝ)] ![(14417348745569/20000000000000 : ℝ), (4636825076259/50000000000000 : ℝ), (4659901526599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7655912167/10000000000 : ℝ)|^87 ≤ (14417348745569/20000000000000 : ℝ)^71
        have hw : |(7655912167/10000000000 : ℝ)|=(7655912167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1436089849/10000000000 : ℝ)|^87 ≤ (4636825076259/50000000000000 : ℝ)^71
        have hw : |(-1436089849/10000000000 : ℝ)|=(1436089849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2538687741/10000000000 : ℝ)|^87 ≤ (4659901526599/25000000000000 : ℝ)^71
        have hw : |(-2538687741/10000000000 : ℝ)|=(2538687741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-277308541/10000000000 : ℝ)*x 0 + (-224748843/500000000 : ℝ)*x 1 + (-670070017/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277308541/10000000000 : ℝ)^87 ≤ (309045007773/25000000000000 : ℝ)^71 := by
    have hnat : (277308541 : ℕ)^87*25000000000000^71 ≤ 309045007773^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277308541 10000000000 309045007773 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224748843/500000000 : ℝ)^87 ≤ (37537803783723/100000000000000 : ℝ)^71 := by
    have hnat : (224748843 : ℕ)^87*100000000000000^71 ≤ 37537803783723^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224748843 500000000 37537803783723 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670070017/1000000000 : ℝ)^87 ≤ (61226016166111/100000000000000 : ℝ)^71 := by
    have hnat : (670070017 : ℕ)^87*100000000000000^71 ≤ 61226016166111^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670070017 1000000000 61226016166111 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277308541/10000000000 : ℝ), (-224748843/500000000 : ℝ), (-670070017/1000000000 : ℝ)] ![(309045007773/25000000000000 : ℝ), (37537803783723/100000000000000 : ℝ), (61226016166111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277308541/10000000000 : ℝ)|^87 ≤ (309045007773/25000000000000 : ℝ)^71
        have hw : |(-277308541/10000000000 : ℝ)|=(277308541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224748843/500000000 : ℝ)|^87 ≤ (37537803783723/100000000000000 : ℝ)^71
        have hw : |(-224748843/500000000 : ℝ)|=(224748843/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-670070017/1000000000 : ℝ)|^87 ≤ (61226016166111/100000000000000 : ℝ)^71
        have hw : |(-670070017/1000000000 : ℝ)|=(670070017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2385483619/5000000000 : ℝ)*x 0 + (849143969/2000000000 : ℝ)*x 1 + (-318543811/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2385483619/5000000000 : ℝ)^87 ≤ (20190622994981/50000000000000 : ℝ)^71 := by
    have hnat : (2385483619 : ℕ)^87*50000000000000^71 ≤ 20190622994981^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385483619 5000000000 20190622994981 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849143969/2000000000 : ℝ)^87 ≤ (7000666296113/20000000000000 : ℝ)^71 := by
    have hnat : (849143969 : ℕ)^87*20000000000000^71 ≤ 7000666296113^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849143969 2000000000 7000666296113 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318543811/1000000000 : ℝ)^87 ≤ (24615422518641/100000000000000 : ℝ)^71 := by
    have hnat : (318543811 : ℕ)^87*100000000000000^71 ≤ 24615422518641^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318543811 1000000000 24615422518641 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2385483619/5000000000 : ℝ), (849143969/2000000000 : ℝ), (-318543811/1000000000 : ℝ)] ![(20190622994981/50000000000000 : ℝ), (7000666296113/20000000000000 : ℝ), (24615422518641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2385483619/5000000000 : ℝ)|^87 ≤ (20190622994981/50000000000000 : ℝ)^71
        have hw : |(2385483619/5000000000 : ℝ)|=(2385483619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849143969/2000000000 : ℝ)|^87 ≤ (7000666296113/20000000000000 : ℝ)^71
        have hw : |(849143969/2000000000 : ℝ)|=(849143969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318543811/1000000000 : ℝ)|^87 ≤ (24615422518641/100000000000000 : ℝ)^71
        have hw : |(-318543811/1000000000 : ℝ)|=(318543811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2725653431/5000000000 : ℝ)*x 0 + (-3824444071/10000000000 : ℝ)*x 1 + (717341837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725653431/5000000000 : ℝ)^87 ≤ (5943339006739/12500000000000 : ℝ)^71 := by
    have hnat : (2725653431 : ℕ)^87*12500000000000^71 ≤ 5943339006739^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725653431 5000000000 5943339006739 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3824444071/10000000000 : ℝ)^87 ≤ (15398173408219/50000000000000 : ℝ)^71 := by
    have hnat : (3824444071 : ℕ)^87*50000000000000^71 ≤ 15398173408219^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824444071 10000000000 15398173408219 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717341837/2500000000 : ℝ)^87 ≤ (10828470559107/50000000000000 : ℝ)^71 := by
    have hnat : (717341837 : ℕ)^87*50000000000000^71 ≤ 10828470559107^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717341837 2500000000 10828470559107 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2725653431/5000000000 : ℝ), (-3824444071/10000000000 : ℝ), (717341837/2500000000 : ℝ)] ![(5943339006739/12500000000000 : ℝ), (15398173408219/50000000000000 : ℝ), (10828470559107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2725653431/5000000000 : ℝ)|^87 ≤ (5943339006739/12500000000000 : ℝ)^71
        have hw : |(2725653431/5000000000 : ℝ)|=(2725653431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3824444071/10000000000 : ℝ)|^87 ≤ (15398173408219/50000000000000 : ℝ)^71
        have hw : |(-3824444071/10000000000 : ℝ)|=(3824444071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(717341837/2500000000 : ℝ)|^87 ≤ (10828470559107/50000000000000 : ℝ)^71
        have hw : |(717341837/2500000000 : ℝ)|=(717341837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_19 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (339674793/400000000 : ℝ)*x 0 + (-1128145241/10000000000 : ℝ)*x 1 + (-168173569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339674793/400000000 : ℝ)^87 ≤ (40923623682541/50000000000000 : ℝ)^71 := by
    have hnat : (339674793 : ℕ)^87*50000000000000^71 ≤ 40923623682541^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339674793 400000000 40923623682541 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128145241/10000000000 : ℝ)^87 ≤ (1379886817153/20000000000000 : ℝ)^71 := by
    have hnat : (1128145241 : ℕ)^87*20000000000000^71 ≤ 1379886817153^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128145241 10000000000 1379886817153 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168173569/1000000000 : ℝ)^87 ≤ (2813329633731/25000000000000 : ℝ)^71 := by
    have hnat : (168173569 : ℕ)^87*25000000000000^71 ≤ 2813329633731^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168173569 1000000000 2813329633731 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339674793/400000000 : ℝ), (-1128145241/10000000000 : ℝ), (-168173569/1000000000 : ℝ)] ![(40923623682541/50000000000000 : ℝ), (1379886817153/20000000000000 : ℝ), (2813329633731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339674793/400000000 : ℝ)|^87 ≤ (40923623682541/50000000000000 : ℝ)^71
        have hw : |(339674793/400000000 : ℝ)|=(339674793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128145241/10000000000 : ℝ)|^87 ≤ (1379886817153/20000000000000 : ℝ)^71
        have hw : |(-1128145241/10000000000 : ℝ)|=(1128145241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168173569/1000000000 : ℝ)|^87 ≤ (2813329633731/25000000000000 : ℝ)^71
        have hw : |(-168173569/1000000000 : ℝ)|=(168173569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769521/62500000 : ℝ)*x 0 + (-4672237141/10000000000 : ℝ)*x 1 + (-3267334613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769521/62500000 : ℝ)^87 ≤ (1268017239387/100000000000000 : ℝ)^71 := by
    have hnat : (1769521 : ℕ)^87*100000000000000^71 ≤ 1268017239387^71*62500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769521 62500000 1268017239387 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4672237141/10000000000 : ℝ)^87 ≤ (39359684665181/100000000000000 : ℝ)^71 := by
    have hnat : (4672237141 : ℕ)^87*100000000000000^71 ≤ 39359684665181^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4672237141 10000000000 39359684665181 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3267334613/5000000000 : ℝ)^87 ≤ (14843074520301/25000000000000 : ℝ)^71 := by
    have hnat : (3267334613 : ℕ)^87*25000000000000^71 ≤ 14843074520301^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3267334613 5000000000 14843074520301 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769521/62500000 : ℝ), (-4672237141/10000000000 : ℝ), (-3267334613/5000000000 : ℝ)] ![(1268017239387/100000000000000 : ℝ), (39359684665181/100000000000000 : ℝ), (14843074520301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769521/62500000 : ℝ)|^87 ≤ (1268017239387/100000000000000 : ℝ)^71
        have hw : |(-1769521/62500000 : ℝ)|=(1769521/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4672237141/10000000000 : ℝ)|^87 ≤ (39359684665181/100000000000000 : ℝ)^71
        have hw : |(-4672237141/10000000000 : ℝ)|=(4672237141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3267334613/5000000000 : ℝ)|^87 ≤ (14843074520301/25000000000000 : ℝ)^71
        have hw : |(-3267334613/5000000000 : ℝ)|=(3267334613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1089098451/2000000000 : ℝ)*x 0 + (3912538141/10000000000 : ℝ)*x 1 + (-695387857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089098451/2000000000 : ℝ)^87 ≤ (47484575249057/100000000000000 : ℝ)^71 := by
    have hnat : (1089098451 : ℕ)^87*100000000000000^71 ≤ 47484575249057^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089098451 2000000000 47484575249057 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3912538141/10000000000 : ℝ)^87 ≤ (31667827107159/100000000000000 : ℝ)^71 := by
    have hnat : (3912538141 : ℕ)^87*100000000000000^71 ≤ 31667827107159^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3912538141 10000000000 31667827107159 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695387857/2500000000 : ℝ)^87 ≤ (20847597642919/100000000000000 : ℝ)^71 := by
    have hnat : (695387857 : ℕ)^87*100000000000000^71 ≤ 20847597642919^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695387857 2500000000 20847597642919 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089098451/2000000000 : ℝ), (3912538141/10000000000 : ℝ), (-695387857/2500000000 : ℝ)] ![(47484575249057/100000000000000 : ℝ), (31667827107159/100000000000000 : ℝ), (20847597642919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089098451/2000000000 : ℝ)|^87 ≤ (47484575249057/100000000000000 : ℝ)^71
        have hw : |(1089098451/2000000000 : ℝ)|=(1089098451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3912538141/10000000000 : ℝ)|^87 ≤ (31667827107159/100000000000000 : ℝ)^71
        have hw : |(3912538141/10000000000 : ℝ)|=(3912538141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-695387857/2500000000 : ℝ)|^87 ≤ (20847597642919/100000000000000 : ℝ)^71
        have hw : |(-695387857/2500000000 : ℝ)|=(695387857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4764406463/10000000000 : ℝ)*x 0 + (-1085840967/2500000000 : ℝ)*x 1 + (3087839539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4764406463/10000000000 : ℝ)^87 ≤ (20156606308141/50000000000000 : ℝ)^71 := by
    have hnat : (4764406463 : ℕ)^87*50000000000000^71 ≤ 20156606308141^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4764406463 10000000000 20156606308141 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085840967/2500000000 : ℝ)^87 ≤ (35992298866001/100000000000000 : ℝ)^71 := by
    have hnat : (1085840967 : ℕ)^87*100000000000000^71 ≤ 35992298866001^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085840967 2500000000 35992298866001 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3087839539/10000000000 : ℝ)^87 ≤ (2961811061757/12500000000000 : ℝ)^71 := by
    have hnat : (3087839539 : ℕ)^87*12500000000000^71 ≤ 2961811061757^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087839539 10000000000 2961811061757 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4764406463/10000000000 : ℝ), (-1085840967/2500000000 : ℝ), (3087839539/10000000000 : ℝ)] ![(20156606308141/50000000000000 : ℝ), (35992298866001/100000000000000 : ℝ), (2961811061757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4764406463/10000000000 : ℝ)|^87 ≤ (20156606308141/50000000000000 : ℝ)^71
        have hw : |(4764406463/10000000000 : ℝ)|=(4764406463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085840967/2500000000 : ℝ)|^87 ≤ (35992298866001/100000000000000 : ℝ)^71
        have hw : |(-1085840967/2500000000 : ℝ)|=(1085840967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3087839539/10000000000 : ℝ)|^87 ≤ (2961811061757/12500000000000 : ℝ)^71
        have hw : |(3087839539/10000000000 : ℝ)|=(3087839539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s0_25 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4255837843/5000000000 : ℝ)*x 0 + (-232117961/2000000000 : ℝ)*x 1 + (-811610183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255837843/5000000000 : ℝ)^87 ≤ (82081222350433/100000000000000 : ℝ)^71 := by
    have hnat : (4255837843 : ℕ)^87*100000000000000^71 ≤ 82081222350433^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255837843 5000000000 82081222350433 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232117961/2000000000 : ℝ)^87 ≤ (3571676663069/50000000000000 : ℝ)^71 := by
    have hnat : (232117961 : ℕ)^87*50000000000000^71 ≤ 3571676663069^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232117961 2000000000 3571676663069 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (811610183/5000000000 : ℝ)^87 ≤ (2693856077223/25000000000000 : ℝ)^71 := by
    have hnat : (811610183 : ℕ)^87*25000000000000^71 ≤ 2693856077223^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811610183 5000000000 2693856077223 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255837843/5000000000 : ℝ), (-232117961/2000000000 : ℝ), (-811610183/5000000000 : ℝ)] ![(82081222350433/100000000000000 : ℝ), (3571676663069/50000000000000 : ℝ), (2693856077223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255837843/5000000000 : ℝ)|^87 ≤ (82081222350433/100000000000000 : ℝ)^71
        have hw : |(4255837843/5000000000 : ℝ)|=(4255837843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232117961/2000000000 : ℝ)|^87 ≤ (3571676663069/50000000000000 : ℝ)^71
        have hw : |(-232117961/2000000000 : ℝ)|=(232117961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-811610183/5000000000 : ℝ)|^87 ≤ (2693856077223/25000000000000 : ℝ)^71
        have hw : |(-811610183/5000000000 : ℝ)|=(811610183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048743047/10000000000 : ℝ)*x 0 + (-2179399067/5000000000 : ℝ)*x 1 + (-563507573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048743047/10000000000 : ℝ)^87 ≤ (7166378610853/50000000000000 : ℝ)^71 := by
    have hnat : (2048743047 : ℕ)^87*50000000000000^71 ≤ 7166378610853^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048743047 10000000000 7166378610853 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179399067/5000000000 : ℝ)^87 ≤ (36149083664899/100000000000000 : ℝ)^71 := by
    have hnat : (2179399067 : ℕ)^87*100000000000000^71 ≤ 36149083664899^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179399067 5000000000 36149083664899 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563507573/1000000000 : ℝ)^87 ≤ (49518159100979/100000000000000 : ℝ)^71 := by
    have hnat : (563507573 : ℕ)^87*100000000000000^71 ≤ 49518159100979^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563507573 1000000000 49518159100979 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048743047/10000000000 : ℝ), (-2179399067/5000000000 : ℝ), (-563507573/1000000000 : ℝ)] ![(7166378610853/50000000000000 : ℝ), (36149083664899/100000000000000 : ℝ), (49518159100979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048743047/10000000000 : ℝ)|^87 ≤ (7166378610853/50000000000000 : ℝ)^71
        have hw : |(-2048743047/10000000000 : ℝ)|=(2048743047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179399067/5000000000 : ℝ)|^87 ≤ (36149083664899/100000000000000 : ℝ)^71
        have hw : |(-2179399067/5000000000 : ℝ)|=(2179399067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563507573/1000000000 : ℝ)|^87 ≤ (49518159100979/100000000000000 : ℝ)^71
        have hw : |(-563507573/1000000000 : ℝ)|=(563507573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (587504947/1250000000 : ℝ)*x 0 + (1034949789/2500000000 : ℝ)*x 1 + (-674887267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587504947/1250000000 : ℝ)^87 ≤ (396468692441/1000000000000 : ℝ)^71 := by
    have hnat : (587504947 : ℕ)^87*1000000000000^71 ≤ 396468692441^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587504947 1250000000 396468692441 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034949789/2500000000 : ℝ)^87 ≤ (33936319608823/100000000000000 : ℝ)^71 := by
    have hnat : (1034949789 : ℕ)^87*100000000000000^71 ≤ 33936319608823^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034949789 2500000000 33936319608823 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674887267/2000000000 : ℝ)^87 ≤ (5283362226249/20000000000000 : ℝ)^71 := by
    have hnat : (674887267 : ℕ)^87*20000000000000^71 ≤ 5283362226249^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674887267 2000000000 5283362226249 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587504947/1250000000 : ℝ), (1034949789/2500000000 : ℝ), (-674887267/2000000000 : ℝ)] ![(396468692441/1000000000000 : ℝ), (33936319608823/100000000000000 : ℝ), (5283362226249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587504947/1250000000 : ℝ)|^87 ≤ (396468692441/1000000000000 : ℝ)^71
        have hw : |(587504947/1250000000 : ℝ)|=(587504947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034949789/2500000000 : ℝ)|^87 ≤ (33936319608823/100000000000000 : ℝ)^71
        have hw : |(1034949789/2500000000 : ℝ)|=(1034949789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-674887267/2000000000 : ℝ)|^87 ≤ (5283362226249/20000000000000 : ℝ)^71
        have hw : |(-674887267/2000000000 : ℝ)|=(674887267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (470022183/1000000000 : ℝ)*x 0 + (-4139693701/10000000000 : ℝ)*x 1 + (3374350377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470022183/1000000000 : ℝ)^87 ≤ (39648753098153/100000000000000 : ℝ)^71 := by
    have hnat : (470022183 : ℕ)^87*100000000000000^71 ≤ 39648753098153^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470022183 1000000000 39648753098153 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139693701/10000000000 : ℝ)^87 ≤ (3393526032509/10000000000000 : ℝ)^71 := by
    have hnat : (4139693701 : ℕ)^87*10000000000000^71 ≤ 3393526032509^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139693701 10000000000 3393526032509 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374350377/10000000000 : ℝ)^87 ≤ (6603996641459/25000000000000 : ℝ)^71 := by
    have hnat : (3374350377 : ℕ)^87*25000000000000^71 ≤ 6603996641459^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374350377 10000000000 6603996641459 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(470022183/1000000000 : ℝ), (-4139693701/10000000000 : ℝ), (3374350377/10000000000 : ℝ)] ![(39648753098153/100000000000000 : ℝ), (3393526032509/10000000000000 : ℝ), (6603996641459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(470022183/1000000000 : ℝ)|^87 ≤ (39648753098153/100000000000000 : ℝ)^71
        have hw : |(470022183/1000000000 : ℝ)|=(470022183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4139693701/10000000000 : ℝ)|^87 ≤ (3393526032509/10000000000000 : ℝ)^71
        have hw : |(-4139693701/10000000000 : ℝ)|=(4139693701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3374350377/10000000000 : ℝ)|^87 ≤ (6603996641459/25000000000000 : ℝ)^71
        have hw : |(3374350377/10000000000 : ℝ)|=(3374350377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325038_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6123789327/10000000000 : ℝ)*x 0 + (-1292663573/5000000000 : ℝ)*x 1 + (-3342323689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6123789327/10000000000 : ℝ)^87 ≤ (5483082784483/10000000000000 : ℝ)^71 := by
    have hnat : (6123789327 : ℕ)^87*10000000000000^71 ≤ 5483082784483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6123789327 10000000000 5483082784483 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292663573/5000000000 : ℝ)^87 ≤ (4765019071187/25000000000000 : ℝ)^71 := by
    have hnat : (1292663573 : ℕ)^87*25000000000000^71 ≤ 4765019071187^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292663573 5000000000 4765019071187 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3342323689/10000000000 : ℝ)^87 ≤ (26109095849723/100000000000000 : ℝ)^71 := by
    have hnat : (3342323689 : ℕ)^87*100000000000000^71 ≤ 26109095849723^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342323689 10000000000 26109095849723 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6123789327/10000000000 : ℝ), (-1292663573/5000000000 : ℝ), (-3342323689/10000000000 : ℝ)] ![(5483082784483/10000000000000 : ℝ), (4765019071187/25000000000000 : ℝ), (26109095849723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6123789327/10000000000 : ℝ)|^87 ≤ (5483082784483/10000000000000 : ℝ)^71
        have hw : |(6123789327/10000000000 : ℝ)|=(6123789327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1292663573/5000000000 : ℝ)|^87 ≤ (4765019071187/25000000000000 : ℝ)^71
        have hw : |(-1292663573/5000000000 : ℝ)|=(1292663573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3342323689/10000000000 : ℝ)|^87 ≤ (26109095849723/100000000000000 : ℝ)^71
        have hw : |(-3342323689/10000000000 : ℝ)|=(3342323689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325038 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-704426663/10000000000 : ℝ)*X 0 0+(-2236715961/5000000000 : ℝ)*X 0 1+(-3241980523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5014690489/10000000000 : ℝ)*X 2 0+(-165830223/400000000 : ℝ)*X 2 1+(3022383119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7730981719/10000000000 : ℝ)*X 0 0+(-397311817/2500000000 : ℝ)*X 0 1+(-460702993/2000000000 : ℝ)*X 0 2+(7730981719/10000000000 : ℝ)*X 1 0+(-397311817/2500000000 : ℝ)*X 1 1+(-460702993/2000000000 : ℝ)*X 1 2+(7730981719/10000000000 : ℝ)*X 2 0+(-397311817/2500000000 : ℝ)*X 2 1+(-460702993/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-340364509/5000000000 : ℝ)*X 0 0+(-4561707261/10000000000 : ℝ)*X 0 1+(-100262911/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((626959893/1250000000 : ℝ)*X 1 0+(4329007377/10000000000 : ℝ)*X 1 1+(-564400709/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5015679017/10000000000 : ℝ)*X 2 0+(-1973081569/5000000000 : ℝ)*X 2 1+(3232801703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_10 : ((1999999997/2000000000 : ℝ)*X 1 0+(73/1000000000 : ℝ)*X 1 1+(1999999997/2000000000 : ℝ)*X 2 0+(73/1000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_10 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7655912167/10000000000 : ℝ)*X 0 0+(-1436089849/10000000000 : ℝ)*X 0 1+(-2538687741/10000000000 : ℝ)*X 0 2+(7655912167/10000000000 : ℝ)*X 1 0+(-1436089849/10000000000 : ℝ)*X 1 1+(-2538687741/10000000000 : ℝ)*X 1 2+(7655912167/10000000000 : ℝ)*X 2 0+(-1436089849/10000000000 : ℝ)*X 2 1+(-2538687741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-277308541/10000000000 : ℝ)*X 0 0+(-224748843/500000000 : ℝ)*X 0 1+(-670070017/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2385483619/5000000000 : ℝ)*X 1 0+(849143969/2000000000 : ℝ)*X 1 1+(-318543811/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2725653431/5000000000 : ℝ)*X 2 0+(-3824444071/10000000000 : ℝ)*X 2 1+(717341837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((339674793/400000000 : ℝ)*X 0 0+(-1128145241/10000000000 : ℝ)*X 0 1+(-168173569/1000000000 : ℝ)*X 0 2+(339674793/400000000 : ℝ)*X 1 0+(-1128145241/10000000000 : ℝ)*X 1 1+(-168173569/1000000000 : ℝ)*X 1 2+(339674793/400000000 : ℝ)*X 2 0+(-1128145241/10000000000 : ℝ)*X 2 1+(-168173569/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1769521/62500000 : ℝ)*X 0 0+(-4672237141/10000000000 : ℝ)*X 0 1+(-3267334613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1089098451/2000000000 : ℝ)*X 1 0+(3912538141/10000000000 : ℝ)*X 1 1+(-695387857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4764406463/10000000000 : ℝ)*X 2 0+(-1085840967/2500000000 : ℝ)*X 2 1+(3087839539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((4255837843/5000000000 : ℝ)*X 0 0+(-232117961/2000000000 : ℝ)*X 0 1+(-811610183/5000000000 : ℝ)*X 0 2+(4255837843/5000000000 : ℝ)*X 1 0+(-232117961/2000000000 : ℝ)*X 1 1+(-811610183/5000000000 : ℝ)*X 1 2+(4255837843/5000000000 : ℝ)*X 2 0+(-232117961/2000000000 : ℝ)*X 2 1+(-811610183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((493/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(493/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4640347631158850854869/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114399823197/62500000000 : ℝ)*(base39) + (389285651269/500000000000 : ℝ)*(base59) + (5093861623347/1000000000000 : ℝ)*(major_s0_0) + (5093861623347/1000000000000 : ℝ)*(major_s0_1) + (5093861623347/1000000000000 : ℝ)*(major_s0_2) + (64384037/500000000000 : ℝ)*(sp_s0_0) + (8445931/200000000000 : ℝ)*(sp_s0_2) + (382627975159/50000000000 : ℝ)*(sp_s0_7) + (7652609311977/1000000000000 : ℝ)*(sp_s0_8) + (3826286648727/500000000000 : ℝ)*(sp_s0_9) + (2535028851217/1000000000000 : ℝ)*(sp_s0_13) + (4577439/1000000000000 : ℝ)*(sp_s0_14) + (20884179/250000000000 : ℝ)*(sp_s0_15) + (4832599/62500000000 : ℝ)*(sp_s0_22) + (2535028851217/1000000000000 : ℝ)*(f.failure) + (7652692848693/1000000000000 : ℝ)*(f.sum) + (192599531515057/5000000000000000000000000000 : ℝ)*base63 + (125380249098357/10000000000000000000000000000 : ℝ)*base65 + (776286717098357/10000000000000000000000000000 : ℝ)*base66 + (682332415515057/10000000000000000000000000000 : ℝ)*base69 + (681347451306707/5000000000000000000000000000 : ℝ)*base71 + (3099110290098357/10000000000000000000000000000 : ℝ)*base73 + (768179106515057/10000000000000000000000000000 : ℝ)*base75 + (137558172515057/10000000000000000000000000000 : ℝ)*base77 + (1803781457/5000000000000000000000 : ℝ)*base79 + (7237/100000000000000000 : ℝ)*base86 + (7237/100000000000000000 : ℝ)*base88 + (7237/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6867/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-6867/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25988516887550978257743/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529562755919/250000000000 : ℝ)*(base39) + (2350011831/1600000000 : ℝ)*(base59) + (23954111921521/1000000000000 : ℝ)*(major_s0_0) + (4891935618693/500000000000 : ℝ)*(major_s0_1) + (4891935618693/500000000000 : ℝ)*(major_s0_2) + (24067149/200000000000 : ℝ)*(sp_s0_0) + (23922359/250000000000 : ℝ)*(sp_s0_9) + (2834048136827/200000000000 : ℝ)*(sp_s0_10) + (20028757/500000000000 : ℝ)*(sp_s0_13) + (2939709019269/200000000000 : ℝ)*(sp_s0_14) + (3674650484487/250000000000 : ℝ)*(sp_s0_15) + (7349284871327/500000000000 : ℝ)*(sp_s0_16) + (2434517626299/500000000000 : ℝ)*(sp_s0_19) + (31747071/500000000000 : ℝ)*(sp_s0_21) + (152158603441/31250000000 : ℝ)*(f.failure) + (1469866543209/100000000000 : ℝ)*(f.sum) + (74159814104183/2500000000000000000000000000 : ℝ)*base63 + (2410871280923117/5000000000000000000000000000 : ℝ)*base64 + (291979534923117/5000000000000000000000000000 : ℝ)*base67 + (90563032395817/5000000000000000000000000000 : ℝ)*base68 + (5445841257013183/10000000000000000000000000000 : ℝ)*base70 + (4270905415554951/10000000000000000000000000000 : ℝ)*base73 + (41682195395817/5000000000000000000000000000 : ℝ)*base74 + (272854082833051/10000000000000000000000000000 : ℝ)*base77 + (740506783080237/2000000000000000000000000000 : ℝ)*base79 + (151/3125000000000000 : ℝ)*base86 + (151/3125000000000000 : ℝ)*base88 + (151/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3403/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3403/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43795166833805495610963/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (279151238463/100000000000 : ℝ)*(base39) + (366374295177/250000000000 : ℝ)*(base59) + (507918032423/25000000000 : ℝ)*(major_s0_0) + (9773224938289/1000000000000 : ℝ)*(major_s0_1) + (9773224938289/1000000000000 : ℝ)*(major_s0_2) + (105416543/500000000000 : ℝ)*(sp_s0_2) + (50488387/1000000000000 : ℝ)*(sp_s0_6) + (148954193/500000000000 : ℝ)*(sp_s0_7) + (61133327/250000000000 : ℝ)*(sp_s0_8) + (1054349635863/100000000000 : ℝ)*(sp_s0_10) + (293647440251/20000000000 : ℝ)*(sp_s0_20) + (3670606346907/250000000000 : ℝ)*(sp_s0_21) + (293649181757/20000000000 : ℝ)*(sp_s0_22) + (2431863273787/500000000000 : ℝ)*(sp_s0_25) + (4863777035961/1000000000000 : ℝ)*(f.failure) + (1835333740117/125000000000 : ℝ)*(f.sum) + (1016990803679941/5000000000000000000000000000 : ℝ)*base62 + (4601348729257159/10000000000000000000000000000 : ℝ)*base65 + (4928796535742841/10000000000000000000000000000 : ℝ)*base67 + (4117241171820059/10000000000000000000000000000 : ℝ)*base69 + (384127145129679/10000000000000000000000000000 : ℝ)*base71 + (92200643691513/250000000000000000000000000 : ℝ)*base73 + (3957497059820059/10000000000000000000000000000 : ℝ)*base75 + (119943485296813/250000000000000000000000000 : ℝ)*base77 + (339938927596639/10000000000000000000000000000 : ℝ)*base78 + (32621/100000000000000000 : ℝ)*base86 + (67379/100000000000000000 : ℝ)*base89 + (67379/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (493/20000 : ℝ) ^ (85/16 : ℝ) ≤ (71526572647/25000000000000000000 : ℝ) := by
    have hpowers : (493/20000 : ℝ)^85 ≤ (71526572647/25000000000000000000 : ℝ)^16 := by
      have hnat : (493 : ℕ)^85*25000000000000000000^16 ≤ 71526572647^16*20000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        493 20000 71526572647 25000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (493/20000 : ℝ)) (X := (71526572647/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25000000071526572647/25000000000000000000 : ℝ) ≤ (10000000005385531/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (25000000071526572647/25000000000000000000 : ℝ)^16 ≤ (10000000005385531/10000000000000000 : ℝ)^85 := by
      have hnat : (25000000071526572647 : ℕ)^16*10000000000000000^85 ≤ 10000000005385531^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000071526572647 25000000000000000000 10000000005385531 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000005385531/10000000000000000 : ℝ)) (X := (25000000071526572647/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12500000071526572647/12500000000000000000 : ℝ) ≤ (10000000010771061/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (12500000071526572647/12500000000000000000 : ℝ)^16 ≤ (10000000010771061/10000000000000000 : ℝ)^85 := by
      have hnat : (12500000071526572647 : ℕ)^16*10000000000000000^85 ≤ 10000000010771061^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000071526572647 12500000000000000000 10000000010771061 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000010771061/10000000000000000 : ℝ)) (X := (12500000071526572647/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5385531/246500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(538553/24650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (493/20000 : ℝ)) (alpha := (5385531/246500000000000 : ℝ)) (beta := (538553/24650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (493/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5385531/246500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(538553/24650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6867/25000 : ℝ) ^ (85/16 : ℝ) ≤ (104416382544561053/100000000000000000000 : ℝ) := by
    have hpowers : (6867/25000 : ℝ)^85 ≤ (104416382544561053/100000000000000000000 : ℝ)^16 := by
      have hnat : (6867 : ℕ)^85*100000000000000000000^16 ≤ 104416382544561053^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6867 25000 104416382544561053 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6867/25000 : ℝ)) (X := (104416382544561053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100104416382544561053/100000000000000000000 : ℝ) ≤ (2000392930477047/2000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100104416382544561053/100000000000000000000 : ℝ)^16 ≤ (2000392930477047/2000000000000000 : ℝ)^85 := by
      have hnat : (100104416382544561053 : ℕ)^16*2000000000000000^85 ≤ 2000392930477047^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100104416382544561053 100000000000000000000 2000392930477047 2000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000392930477047/2000000000000000 : ℝ)) (X := (100104416382544561053/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50104416382544561053/50000000000000000000 : ℝ) ≤ (2500981910485407/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50104416382544561053/50000000000000000000 : ℝ)^16 ≤ (2500981910485407/2500000000000000 : ℝ)^85 := by
      have hnat : (50104416382544561053 : ℕ)^16*2500000000000000^85 ≤ 2500981910485407^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104416382544561053 50000000000000000000 2500981910485407 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500981910485407/2500000000000000 : ℝ)) (X := (50104416382544561053/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(392930477047/549360000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(654329852131/915600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (6867/25000 : ℝ)) (alpha := (392930477047/549360000000000 : ℝ)) (beta := (654329852131/915600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6867/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(392930477047/549360000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(654329852131/915600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3403/12500 : ℝ) ^ (85/16 : ℝ) ≤ (24895575443672607/25000000000000000000 : ℝ) := by
    have hpowers : (3403/12500 : ℝ)^85 ≤ (24895575443672607/25000000000000000000 : ℝ)^16 := by
      have hnat : (3403 : ℕ)^85*25000000000000000000^16 ≤ 24895575443672607^16*12500^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3403 12500 24895575443672607 25000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3403/12500 : ℝ)) (X := (24895575443672607/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25024895575443672607/25000000000000000000 : ℝ) ≤ (10001873733197049/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (25024895575443672607/25000000000000000000 : ℝ)^16 ≤ (10001873733197049/10000000000000000 : ℝ)^85 := by
      have hnat : (25024895575443672607 : ℕ)^16*10000000000000000^85 ≤ 10001873733197049^85*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024895575443672607 25000000000000000000 10001873733197049 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001873733197049/10000000000000000 : ℝ)) (X := (25024895575443672607/25000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12524895575443672607/12500000000000000000 : ℝ) ≤ (2500936488458567/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (12524895575443672607/12500000000000000000 : ℝ)^16 ≤ (2500936488458567/2500000000000000 : ℝ)^85 := by
      have hnat : (12524895575443672607 : ℕ)^16*2500000000000000^85 ≤ 2500936488458567^85*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12524895575443672607 12500000000000000000 2500936488458567 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500936488458567/2500000000000000 : ℝ)) (X := (12524895575443672607/12500000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1873733197049/2722400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1872220637219/2722400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (3403/12500 : ℝ)) (alpha := (1873733197049/2722400000000000 : ℝ)) (beta := (1872220637219/2722400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3403/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1873733197049/2722400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1872220637219/2722400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2048743047/10000000000 : ℝ)*X 0 0+(-2179399067/5000000000 : ℝ)*X 0 1+(-563507573/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((587504947/1250000000 : ℝ)*X 1 0+(1034949789/2500000000 : ℝ)*X 1 1+(-674887267/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((470022183/1000000000 : ℝ)*X 2 0+(-4139693701/10000000000 : ℝ)*X 2 1+(3374350377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6123789327/10000000000 : ℝ)*X 0 0+(-1292663573/5000000000 : ℝ)*X 0 1+(-3342323689/10000000000 : ℝ)*X 0 2+(6123789327/10000000000 : ℝ)*X 1 0+(-1292663573/5000000000 : ℝ)*X 1 1+(-3342323689/10000000000 : ℝ)*X 1 2+(6123789327/10000000000 : ℝ)*X 2 0+(-1292663573/5000000000 : ℝ)*X 2 1+(-3342323689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325038_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-2142318259421555481319095631537549/240012951937500000000000000000000 : ℝ) := by norm_num
    linear_combination (1027/1000000000000 : ℝ)*(base8) + (273/500000000000 : ℝ)*(base33) + (1190349651027/1000000000000 : ℝ)*(base39) + (259590925049/500000000000 : ℝ)*(base40) + (107/200000000000 : ℝ)*(base49) + (14144071291/31250000000 : ℝ)*(base59) + (502347500101/250000000000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (1487640729353/500000000000 : ℝ)*(sp_s1_0) + (743820364559/250000000000 : ℝ)*(sp_s1_1) + (74382036457/25000000000 : ℝ)*(sp_s1_2) + (1000000000951/1000000000000 : ℝ)*(sp_s1_6) + (1487640729391/500000000000 : ℝ)*(f.sum) + (15423493447867159/46736802000000000000000000000 : ℝ)*base62 + (428715011327/680600000000000000000000 : ℝ)*base65 + (2916801103891/22890000000000000000000000 : ℝ)*base67 + (24977430922939/34030000000000000000000000 : ℝ)*base68 + (27346770376867041/104854937500000000000000000000 : ℝ)*base70 + (8029707657447/24650000000000000000000000 : ℝ)*base73 + (3101826751372859/68670000000000000000000000 : ℝ)*base74 + (18788903079947/30812500000000000000000000 : ℝ)*base76 + (6956758138607483/56423850000000000000000000000 : ℝ)*base79 + (951/1000000000000 : ℝ)*base81 + (11/250000000000 : ℝ)*base85 + (19/20000000000 : ℝ)*base86 + (951/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b018 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=38 := by omega
  rcases hc with rfl
  · exact collision_c325038 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 38 ≤ c.val) (hhi : c.val < 39)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
