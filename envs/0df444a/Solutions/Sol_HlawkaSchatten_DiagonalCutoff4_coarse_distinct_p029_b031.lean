-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:25.259388+00:00
-- url     : https://prove2.me/submissions/bfa86d85-8a24-4929-bd0f-54d332999168

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
theorem collision_support_c329062_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-23904211/500000000 : ℝ)*x 0 + (205616203/400000000 : ℝ)*x 1 + (-182853893/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23904211/500000000 : ℝ)^95 ≤ (645657608263/25000000000000 : ℝ)^79 := by
    have hnat : (23904211 : ℕ)^95*25000000000000^79 ≤ 645657608263^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23904211 500000000 645657608263 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205616203/400000000 : ℝ)^95 ≤ (8984525709933/20000000000000 : ℝ)^79 := by
    have hnat : (205616203 : ℕ)^95*20000000000000^79 ≤ 8984525709933^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205616203 400000000 8984525709933 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182853893/312500000 : ℝ)^95 ≤ (52494740994367/100000000000000 : ℝ)^79 := by
    have hnat : (182853893 : ℕ)^95*100000000000000^79 ≤ 52494740994367^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182853893 312500000 52494740994367 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23904211/500000000 : ℝ), (205616203/400000000 : ℝ), (-182853893/312500000 : ℝ)] ![(645657608263/25000000000000 : ℝ), (8984525709933/20000000000000 : ℝ), (52494740994367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23904211/500000000 : ℝ)|^95 ≤ (645657608263/25000000000000 : ℝ)^79
        have hw : |(-23904211/500000000 : ℝ)|=(23904211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205616203/400000000 : ℝ)|^95 ≤ (8984525709933/20000000000000 : ℝ)^79
        have hw : |(205616203/400000000 : ℝ)|=(205616203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182853893/312500000 : ℝ)|^95 ≤ (52494740994367/100000000000000 : ℝ)^79
        have hw : |(-182853893/312500000 : ℝ)|=(182853893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5140404937/10000000000 : ℝ)*x 0 + (-59760511/1250000000 : ℝ)*x 1 + (-5851324791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5140404937/10000000000 : ℝ)^95 ≤ (44922627099413/100000000000000 : ℝ)^79 := by
    have hnat : (5140404937 : ℕ)^95*100000000000000^79 ≤ 44922627099413^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140404937 10000000000 44922627099413 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59760511/1250000000 : ℝ)^95 ≤ (2582629575563/100000000000000 : ℝ)^79 := by
    have hnat : (59760511 : ℕ)^95*100000000000000^79 ≤ 2582629575563^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59760511 1250000000 2582629575563 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5851324791/10000000000 : ℝ)^95 ≤ (52494743313879/100000000000000 : ℝ)^79 := by
    have hnat : (5851324791 : ℕ)^95*100000000000000^79 ≤ 52494743313879^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5851324791 10000000000 52494743313879 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5140404937/10000000000 : ℝ), (-59760511/1250000000 : ℝ), (-5851324791/10000000000 : ℝ)] ![(44922627099413/100000000000000 : ℝ), (2582629575563/100000000000000 : ℝ), (52494743313879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5140404937/10000000000 : ℝ)|^95 ≤ (44922627099413/100000000000000 : ℝ)^79
        have hw : |(5140404937/10000000000 : ℝ)|=(5140404937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59760511/1250000000 : ℝ)|^95 ≤ (2582629575563/100000000000000 : ℝ)^79
        have hw : |(-59760511/1250000000 : ℝ)|=(59760511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5851324791/10000000000 : ℝ)|^95 ≤ (52494743313879/100000000000000 : ℝ)^79
        have hw : |(-5851324791/10000000000 : ℝ)|=(5851324791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2570202701/5000000000 : ℝ)*x 0 + (339471177/625000000 : ℝ)*x 1 + (1105617613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2570202701/5000000000 : ℝ)^95 ≤ (44922631986131/100000000000000 : ℝ)^79 := by
    have hnat : (2570202701 : ℕ)^95*100000000000000^79 ≤ 44922631986131^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570202701 5000000000 44922631986131 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339471177/625000000 : ℝ)^95 ≤ (47999463729239/100000000000000 : ℝ)^79 := by
    have hnat : (339471177 : ℕ)^95*100000000000000^79 ≤ 47999463729239^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339471177 625000000 47999463729239 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105617613/10000000000 : ℝ)^95 ≤ (1769476069929/25000000000000 : ℝ)^79 := by
    have hnat : (1105617613 : ℕ)^95*25000000000000^79 ≤ 1769476069929^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105617613 10000000000 1769476069929 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2570202701/5000000000 : ℝ), (339471177/625000000 : ℝ), (1105617613/10000000000 : ℝ)] ![(44922631986131/100000000000000 : ℝ), (47999463729239/100000000000000 : ℝ), (1769476069929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2570202701/5000000000 : ℝ)|^95 ≤ (44922631986131/100000000000000 : ℝ)^79
        have hw : |(2570202701/5000000000 : ℝ)|=(2570202701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339471177/625000000 : ℝ)|^95 ≤ (47999463729239/100000000000000 : ℝ)^79
        have hw : |(339471177/625000000 : ℝ)|=(339471177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105617613/10000000000 : ℝ)|^95 ≤ (1769476069929/25000000000000 : ℝ)^79
        have hw : |(1105617613/10000000000 : ℝ)|=(1105617613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-14188211/80000000 : ℝ)*x 0 + (704380793/5000000000 : ℝ)*x 1 + (-4068126191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14188211/80000000 : ℝ)^95 ≤ (6247028816301/50000000000000 : ℝ)^79 := by
    have hnat : (14188211 : ℕ)^95*50000000000000^79 ≤ 6247028816301^79*80000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14188211 80000000 6247028816301 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704380793/5000000000 : ℝ)^95 ≤ (1184023091181/12500000000000 : ℝ)^79 := by
    have hnat : (704380793 : ℕ)^95*12500000000000^79 ≤ 1184023091181^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704380793 5000000000 1184023091181 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4068126191/5000000000 : ℝ)^95 ≤ (7803375763001/10000000000000 : ℝ)^79 := by
    have hnat : (4068126191 : ℕ)^95*10000000000000^79 ≤ 7803375763001^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068126191 5000000000 7803375763001 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14188211/80000000 : ℝ), (704380793/5000000000 : ℝ), (-4068126191/5000000000 : ℝ)] ![(6247028816301/50000000000000 : ℝ), (1184023091181/12500000000000 : ℝ), (7803375763001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14188211/80000000 : ℝ)|^95 ≤ (6247028816301/50000000000000 : ℝ)^79
        have hw : |(-14188211/80000000 : ℝ)|=(14188211/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(704380793/5000000000 : ℝ)|^95 ≤ (1184023091181/12500000000000 : ℝ)^79
        have hw : |(704380793/5000000000 : ℝ)|=(704380793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4068126191/5000000000 : ℝ)|^95 ≤ (7803375763001/10000000000000 : ℝ)^79
        have hw : |(-4068126191/5000000000 : ℝ)|=(4068126191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1242751437/5000000000 : ℝ)*x 0 + (-573997173/10000000000 : ℝ)*x 1 + (-2034063347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1242751437/5000000000 : ℝ)^95 ≤ (18748499986259/100000000000000 : ℝ)^79 := by
    have hnat : (1242751437 : ℕ)^95*100000000000000^79 ≤ 18748499986259^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242751437 5000000000 18748499986259 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573997173/10000000000 : ℝ)^95 ≤ (3217730769929/100000000000000 : ℝ)^79 := by
    have hnat : (573997173 : ℕ)^95*100000000000000^79 ≤ 3217730769929^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573997173 10000000000 3217730769929 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2034063347/2500000000 : ℝ)^95 ≤ (39016884616269/50000000000000 : ℝ)^79 := by
    have hnat : (2034063347 : ℕ)^95*50000000000000^79 ≤ 39016884616269^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034063347 2500000000 39016884616269 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1242751437/5000000000 : ℝ), (-573997173/10000000000 : ℝ), (-2034063347/2500000000 : ℝ)] ![(18748499986259/100000000000000 : ℝ), (3217730769929/100000000000000 : ℝ), (39016884616269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1242751437/5000000000 : ℝ)|^95 ≤ (18748499986259/100000000000000 : ℝ)^79
        have hw : |(1242751437/5000000000 : ℝ)|=(1242751437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-573997173/10000000000 : ℝ)|^95 ≤ (3217730769929/100000000000000 : ℝ)^79
        have hw : |(-573997173/10000000000 : ℝ)|=(573997173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2034063347/2500000000 : ℝ)|^95 ≤ (39016884616269/50000000000000 : ℝ)^79
        have hw : |(-2034063347/2500000000 : ℝ)|=(2034063347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2485503283/10000000000 : ℝ)*x 0 + (7564580463/10000000000 : ℝ)*x 1 + (1444661711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2485503283/10000000000 : ℝ)^95 ≤ (4687125924061/25000000000000 : ℝ)^79 := by
    have hnat : (2485503283 : ℕ)^95*25000000000000^79 ≤ 4687125924061^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485503283 10000000000 4687125924061 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7564580463/10000000000 : ℝ)^95 ≤ (71488295502009/100000000000000 : ℝ)^79 := by
    have hnat : (7564580463 : ℕ)^95*100000000000000^79 ≤ 71488295502009^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7564580463 10000000000 71488295502009 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444661711/10000000000 : ℝ)^95 ≤ (9763200781367/100000000000000 : ℝ)^79 := by
    have hnat : (1444661711 : ℕ)^95*100000000000000^79 ≤ 9763200781367^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444661711 10000000000 9763200781367 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2485503283/10000000000 : ℝ), (7564580463/10000000000 : ℝ), (1444661711/10000000000 : ℝ)] ![(4687125924061/25000000000000 : ℝ), (71488295502009/100000000000000 : ℝ), (9763200781367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2485503283/10000000000 : ℝ)|^95 ≤ (4687125924061/25000000000000 : ℝ)^79
        have hw : |(2485503283/10000000000 : ℝ)|=(2485503283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7564580463/10000000000 : ℝ)|^95 ≤ (71488295502009/100000000000000 : ℝ)^79
        have hw : |(7564580463/10000000000 : ℝ)|=(7564580463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1444661711/10000000000 : ℝ)|^95 ≤ (9763200781367/100000000000000 : ℝ)^79
        have hw : |(1444661711/10000000000 : ℝ)|=(1444661711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3660355173/10000000000 : ℝ)*x 0 + (7445211297/10000000000 : ℝ)*x 1 + (-1057971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3660355173/10000000000 : ℝ)^95 ≤ (29862273532509/100000000000000 : ℝ)^79 := by
    have hnat : (3660355173 : ℕ)^95*100000000000000^79 ≤ 29862273532509^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660355173 10000000000 29862273532509 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7445211297/10000000000 : ℝ)^95 ≤ (35066956576271/50000000000000 : ℝ)^79 := by
    have hnat : (7445211297 : ℕ)^95*50000000000000^79 ≤ 35066956576271^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7445211297 10000000000 35066956576271 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057971/5000000000 : ℝ)^95 ≤ (953327229/25000000000000 : ℝ)^79 := by
    have hnat : (1057971 : ℕ)^95*25000000000000^79 ≤ 953327229^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057971 5000000000 953327229 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3660355173/10000000000 : ℝ), (7445211297/10000000000 : ℝ), (-1057971/5000000000 : ℝ)] ![(29862273532509/100000000000000 : ℝ), (35066956576271/50000000000000 : ℝ), (953327229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3660355173/10000000000 : ℝ)|^95 ≤ (29862273532509/100000000000000 : ℝ)^79
        have hw : |(3660355173/10000000000 : ℝ)|=(3660355173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7445211297/10000000000 : ℝ)|^95 ≤ (35066956576271/50000000000000 : ℝ)^79
        have hw : |(7445211297/10000000000 : ℝ)|=(7445211297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057971/5000000000 : ℝ)|^95 ≤ (953327229/25000000000000 : ℝ)^79
        have hw : |(-1057971/5000000000 : ℝ)|=(1057971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10579217/200000000 : ℝ)*x 0 + (604215889/2500000000 : ℝ)*x 1 + (-4108058133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10579217/200000000 : ℝ)^95 ≤ (2916596810713/100000000000000 : ℝ)^79 := by
    have hnat : (10579217 : ℕ)^95*100000000000000^79 ≤ 2916596810713^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10579217 200000000 2916596810713 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604215889/2500000000 : ℝ)^95 ≤ (2265954502941/12500000000000 : ℝ)^79 := by
    have hnat : (604215889 : ℕ)^95*12500000000000^79 ≤ 2265954502941^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604215889 2500000000 2265954502941 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4108058133/5000000000 : ℝ)^95 ≤ (15791153430507/20000000000000 : ℝ)^79 := by
    have hnat : (4108058133 : ℕ)^95*20000000000000^79 ≤ 15791153430507^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108058133 5000000000 15791153430507 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10579217/200000000 : ℝ), (604215889/2500000000 : ℝ), (-4108058133/5000000000 : ℝ)] ![(2916596810713/100000000000000 : ℝ), (2265954502941/12500000000000 : ℝ), (15791153430507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10579217/200000000 : ℝ)|^95 ≤ (2916596810713/100000000000000 : ℝ)^79
        have hw : |(-10579217/200000000 : ℝ)|=(10579217/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604215889/2500000000 : ℝ)|^95 ≤ (2265954502941/12500000000000 : ℝ)^79
        have hw : |(604215889/2500000000 : ℝ)|=(604215889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4108058133/5000000000 : ℝ)|^95 ≤ (15791153430507/20000000000000 : ℝ)^79
        have hw : |(-4108058133/5000000000 : ℝ)|=(4108058133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1284031863/10000000000 : ℝ)*x 0 + (-1782637979/10000000000 : ℝ)*x 1 + (-4108058333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284031863/10000000000 : ℝ)^95 ≤ (8472941166983/100000000000000 : ℝ)^79 := by
    have hnat : (1284031863 : ℕ)^95*100000000000000^79 ≤ 8472941166983^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284031863 10000000000 8472941166983 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782637979/10000000000 : ℝ)^95 ≤ (6285643527207/50000000000000 : ℝ)^79 := by
    have hnat : (1782637979 : ℕ)^95*50000000000000^79 ≤ 6285643527207^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782637979 10000000000 6285643527207 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4108058333/5000000000 : ℝ)^95 ≤ (39477885887501/50000000000000 : ℝ)^79 := by
    have hnat : (4108058333 : ℕ)^95*50000000000000^79 ≤ 39477885887501^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108058333 5000000000 39477885887501 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1284031863/10000000000 : ℝ), (-1782637979/10000000000 : ℝ), (-4108058333/5000000000 : ℝ)] ![(8472941166983/100000000000000 : ℝ), (6285643527207/50000000000000 : ℝ), (39477885887501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1284031863/10000000000 : ℝ)|^95 ≤ (8472941166983/100000000000000 : ℝ)^79
        have hw : |(1284031863/10000000000 : ℝ)|=(1284031863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782637979/10000000000 : ℝ)|^95 ≤ (6285643527207/50000000000000 : ℝ)^79
        have hw : |(-1782637979/10000000000 : ℝ)|=(1782637979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4108058333/5000000000 : ℝ)|^95 ≤ (39477885887501/50000000000000 : ℝ)^79
        have hw : |(-4108058333/5000000000 : ℝ)|=(4108058333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7252870449/10000000000 : ℝ)*x 0 + (2854863387/10000000000 : ℝ)*x 1 + (1460454149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7252870449/10000000000 : ℝ)^95 ≤ (33980422081329/50000000000000 : ℝ)^79 := by
    have hnat : (7252870449 : ℕ)^95*50000000000000^79 ≤ 33980422081329^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7252870449 10000000000 33980422081329 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854863387/10000000000 : ℝ)^95 ≤ (11073735255453/50000000000000 : ℝ)^79 := by
    have hnat : (2854863387 : ℕ)^95*50000000000000^79 ≤ 11073735255453^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854863387 10000000000 11073735255453 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460454149/10000000000 : ℝ)^95 ≤ (4945842658659/50000000000000 : ℝ)^79 := by
    have hnat : (1460454149 : ℕ)^95*50000000000000^79 ≤ 4945842658659^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460454149 10000000000 4945842658659 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7252870449/10000000000 : ℝ), (2854863387/10000000000 : ℝ), (1460454149/10000000000 : ℝ)] ![(33980422081329/50000000000000 : ℝ), (11073735255453/50000000000000 : ℝ), (4945842658659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7252870449/10000000000 : ℝ)|^95 ≤ (33980422081329/50000000000000 : ℝ)^79
        have hw : |(7252870449/10000000000 : ℝ)|=(7252870449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854863387/10000000000 : ℝ)|^95 ≤ (11073735255453/50000000000000 : ℝ)^79
        have hw : |(2854863387/10000000000 : ℝ)|=(2854863387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1460454149/10000000000 : ℝ)|^95 ≤ (4945842658659/50000000000000 : ℝ)^79
        have hw : |(1460454149/10000000000 : ℝ)|=(1460454149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7833438661/10000000000 : ℝ)*x 0 + (3203501647/10000000000 : ℝ)*x 1 + (-658977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7833438661/10000000000 : ℝ)^95 ≤ (74554602951823/100000000000000 : ℝ)^79 := by
    have hnat : (7833438661 : ℕ)^95*100000000000000^79 ≤ 74554602951823^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7833438661 10000000000 74554602951823 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3203501647/10000000000 : ℝ)^95 ≤ (25438901840227/100000000000000 : ℝ)^79 := by
    have hnat : (3203501647 : ℕ)^95*100000000000000^79 ≤ 25438901840227^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3203501647 10000000000 25438901840227 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658977/2000000000 : ℝ)^95 ≤ (6495202853/100000000000000 : ℝ)^79 := by
    have hnat : (658977 : ℕ)^95*100000000000000^79 ≤ 6495202853^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658977 2000000000 6495202853 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7833438661/10000000000 : ℝ), (3203501647/10000000000 : ℝ), (-658977/2000000000 : ℝ)] ![(74554602951823/100000000000000 : ℝ), (25438901840227/100000000000000 : ℝ), (6495202853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7833438661/10000000000 : ℝ)|^95 ≤ (74554602951823/100000000000000 : ℝ)^79
        have hw : |(7833438661/10000000000 : ℝ)|=(7833438661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3203501647/10000000000 : ℝ)|^95 ≤ (25438901840227/100000000000000 : ℝ)^79
        have hw : |(3203501647/10000000000 : ℝ)|=(3203501647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658977/2000000000 : ℝ)|^95 ≤ (6495202853/100000000000000 : ℝ)^79
        have hw : |(-658977/2000000000 : ℝ)|=(658977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1185017/10000000000 : ℝ)*x 0 + (3318615233/5000000000 : ℝ)*x 1 + (-912354437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1185017/10000000000 : ℝ)^95 ≤ (189902009/10000000000000 : ℝ)^79 := by
    have hnat : (1185017 : ℕ)^95*10000000000000^79 ≤ 189902009^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185017 10000000000 189902009 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3318615233/5000000000 : ℝ)^95 ≤ (12216972806463/20000000000000 : ℝ)^79 := by
    have hnat : (3318615233 : ℕ)^95*20000000000000^79 ≤ 12216972806463^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3318615233 5000000000 12216972806463 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912354437/2000000000 : ℝ)^95 ≤ (19456618469479/50000000000000 : ℝ)^79 := by
    have hnat : (912354437 : ℕ)^95*50000000000000^79 ≤ 19456618469479^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912354437 2000000000 19456618469479 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1185017/10000000000 : ℝ), (3318615233/5000000000 : ℝ), (-912354437/2000000000 : ℝ)] ![(189902009/10000000000000 : ℝ), (12216972806463/20000000000000 : ℝ), (19456618469479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1185017/10000000000 : ℝ)|^95 ≤ (189902009/10000000000000 : ℝ)^79
        have hw : |(-1185017/10000000000 : ℝ)|=(1185017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3318615233/5000000000 : ℝ)|^95 ≤ (12216972806463/20000000000000 : ℝ)^79
        have hw : |(3318615233/5000000000 : ℝ)|=(3318615233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912354437/2000000000 : ℝ)|^95 ≤ (19456618469479/50000000000000 : ℝ)^79
        have hw : |(-912354437/2000000000 : ℝ)|=(912354437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7392147821/10000000000 : ℝ)*x 0 + (-151221139/2000000000 : ℝ)*x 1 + (-1630286501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7392147821/10000000000 : ℝ)^95 ≤ (34766626310821/50000000000000 : ℝ)^79 := by
    have hnat : (7392147821 : ℕ)^95*50000000000000^79 ≤ 34766626310821^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7392147821 10000000000 34766626310821 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151221139/2000000000 : ℝ)^95 ≤ (4481877472203/100000000000000 : ℝ)^79 := by
    have hnat : (151221139 : ℕ)^95*100000000000000^79 ≤ 4481877472203^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151221139 2000000000 4481877472203 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1630286501/5000000000 : ℝ)^95 ≤ (25984869889471/100000000000000 : ℝ)^79 := by
    have hnat : (1630286501 : ℕ)^95*100000000000000^79 ≤ 25984869889471^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630286501 5000000000 25984869889471 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7392147821/10000000000 : ℝ), (-151221139/2000000000 : ℝ), (-1630286501/5000000000 : ℝ)] ![(34766626310821/50000000000000 : ℝ), (4481877472203/100000000000000 : ℝ), (25984869889471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7392147821/10000000000 : ℝ)|^95 ≤ (34766626310821/50000000000000 : ℝ)^79
        have hw : |(7392147821/10000000000 : ℝ)|=(7392147821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151221139/2000000000 : ℝ)|^95 ≤ (4481877472203/100000000000000 : ℝ)^79
        have hw : |(-151221139/2000000000 : ℝ)|=(151221139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1630286501/5000000000 : ℝ)|^95 ≤ (25984869889471/100000000000000 : ℝ)^79
        have hw : |(-1630286501/5000000000 : ℝ)|=(1630286501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1634940011/10000000000 : ℝ)*x 0 + (3510164687/5000000000 : ℝ)*x 1 + (745035533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1634940011/10000000000 : ℝ)^95 ≤ (177023563157/1562500000000 : ℝ)^79 := by
    have hnat : (1634940011 : ℕ)^95*1562500000000^79 ≤ 177023563157^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634940011 10000000000 177023563157 1562500000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3510164687/5000000000 : ℝ)^95 ≤ (3267458062219/5000000000000 : ℝ)^79 := by
    have hnat : (3510164687 : ℕ)^95*5000000000000^79 ≤ 3267458062219^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3510164687 5000000000 3267458062219 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745035533/2500000000 : ℝ)^95 ≤ (23321330693787/100000000000000 : ℝ)^79 := by
    have hnat : (745035533 : ℕ)^95*100000000000000^79 ≤ 23321330693787^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745035533 2500000000 23321330693787 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1634940011/10000000000 : ℝ), (3510164687/5000000000 : ℝ), (745035533/2500000000 : ℝ)] ![(177023563157/1562500000000 : ℝ), (3267458062219/5000000000000 : ℝ), (23321330693787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1634940011/10000000000 : ℝ)|^95 ≤ (177023563157/1562500000000 : ℝ)^79
        have hw : |(1634940011/10000000000 : ℝ)|=(1634940011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3510164687/5000000000 : ℝ)|^95 ≤ (3267458062219/5000000000000 : ℝ)^79
        have hw : |(3510164687/5000000000 : ℝ)|=(3510164687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(745035533/2500000000 : ℝ)|^95 ≤ (23321330693787/100000000000000 : ℝ)^79
        have hw : |(745035533/2500000000 : ℝ)|=(745035533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8185148359/10000000000 : ℝ)*x 0 + (81478787/312500000 : ℝ)*x 1 + (-311527203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8185148359/10000000000 : ℝ)^95 ≤ (78598033590919/100000000000000 : ℝ)^79 := by
    have hnat : (8185148359 : ℕ)^95*100000000000000^79 ≤ 78598033590919^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8185148359 10000000000 78598033590919 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81478787/312500000 : ℝ)^95 ≤ (19858911999867/100000000000000 : ℝ)^79 := by
    have hnat : (81478787 : ℕ)^95*100000000000000^79 ≤ 19858911999867^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81478787 312500000 19858911999867 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311527203/10000000000 : ℝ)^95 ≤ (48220449947/3125000000000 : ℝ)^79 := by
    have hnat : (311527203 : ℕ)^95*3125000000000^79 ≤ 48220449947^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311527203 10000000000 48220449947 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8185148359/10000000000 : ℝ), (81478787/312500000 : ℝ), (-311527203/10000000000 : ℝ)] ![(78598033590919/100000000000000 : ℝ), (19858911999867/100000000000000 : ℝ), (48220449947/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8185148359/10000000000 : ℝ)|^95 ≤ (78598033590919/100000000000000 : ℝ)^79
        have hw : |(8185148359/10000000000 : ℝ)|=(8185148359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81478787/312500000 : ℝ)|^95 ≤ (19858911999867/100000000000000 : ℝ)^79
        have hw : |(81478787/312500000 : ℝ)|=(81478787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-311527203/10000000000 : ℝ)|^95 ≤ (48220449947/3125000000000 : ℝ)^79
        have hw : |(-311527203/10000000000 : ℝ)|=(311527203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1420815249/10000000000 : ℝ)*x 0 + (1234586697/2500000000 : ℝ)*x 1 + (-5396047183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1420815249/10000000000 : ℝ)^95 ≤ (9569729389167/100000000000000 : ℝ)^79 := by
    have hnat : (1420815249 : ℕ)^95*100000000000000^79 ≤ 9569729389167^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420815249 10000000000 9569729389167 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234586697/2500000000 : ℝ)^95 ≤ (42807726020699/100000000000000 : ℝ)^79 := by
    have hnat : (1234586697 : ℕ)^95*100000000000000^79 ≤ 42807726020699^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234586697 2500000000 42807726020699 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396047183/10000000000 : ℝ)^95 ≤ (9524508913563/20000000000000 : ℝ)^79 := by
    have hnat : (5396047183 : ℕ)^95*20000000000000^79 ≤ 9524508913563^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396047183 10000000000 9524508913563 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1420815249/10000000000 : ℝ), (1234586697/2500000000 : ℝ), (-5396047183/10000000000 : ℝ)] ![(9569729389167/100000000000000 : ℝ), (42807726020699/100000000000000 : ℝ), (9524508913563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1420815249/10000000000 : ℝ)|^95 ≤ (9569729389167/100000000000000 : ℝ)^79
        have hw : |(-1420815249/10000000000 : ℝ)|=(1420815249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1234586697/2500000000 : ℝ)|^95 ≤ (42807726020699/100000000000000 : ℝ)^79
        have hw : |(1234586697/2500000000 : ℝ)|=(1234586697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5396047183/10000000000 : ℝ)|^95 ≤ (9524508913563/20000000000000 : ℝ)^79
        have hw : |(-5396047183/10000000000 : ℝ)|=(5396047183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4939296599/10000000000 : ℝ)*x 0 + (-355053049/2500000000 : ℝ)*x 1 + (-1079114893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4939296599/10000000000 : ℝ)^95 ≤ (4281762710461/10000000000000 : ℝ)^79 := by
    have hnat : (4939296599 : ℕ)^95*10000000000000^79 ≤ 4281762710461^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939296599 10000000000 4281762710461 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355053049/2500000000 : ℝ)^95 ≤ (9564845167401/100000000000000 : ℝ)^79 := by
    have hnat : (355053049 : ℕ)^95*100000000000000^79 ≤ 9564845167401^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355053049 2500000000 9564845167401 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079114893/2000000000 : ℝ)^95 ≤ (47617527711543/100000000000000 : ℝ)^79 := by
    have hnat : (1079114893 : ℕ)^95*100000000000000^79 ≤ 47617527711543^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079114893 2000000000 47617527711543 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4939296599/10000000000 : ℝ), (-355053049/2500000000 : ℝ), (-1079114893/2000000000 : ℝ)] ![(4281762710461/10000000000000 : ℝ), (9564845167401/100000000000000 : ℝ), (47617527711543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4939296599/10000000000 : ℝ)|^95 ≤ (4281762710461/10000000000000 : ℝ)^79
        have hw : |(4939296599/10000000000 : ℝ)|=(4939296599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355053049/2500000000 : ℝ)|^95 ≤ (9564845167401/100000000000000 : ℝ)^79
        have hw : |(-355053049/2500000000 : ℝ)|=(355053049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079114893/2000000000 : ℝ)|^95 ≤ (47617527711543/100000000000000 : ℝ)^79
        have hw : |(-1079114893/2000000000 : ℝ)|=(1079114893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (156016797/312500000 : ℝ)*x 0 + (1248445211/2500000000 : ℝ)*x 1 + (1861208517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156016797/312500000 : ℝ)^95 ≤ (21686619719101/50000000000000 : ℝ)^79 := by
    have hnat : (156016797 : ℕ)^95*50000000000000^79 ≤ 21686619719101^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156016797 312500000 21686619719101 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248445211/2500000000 : ℝ)^95 ≤ (1355819659423/3125000000000 : ℝ)^79 := by
    have hnat : (1248445211 : ℕ)^95*3125000000000^79 ≤ 1355819659423^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248445211 2500000000 1355819659423 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861208517/10000000000 : ℝ)^95 ≤ (6620265726177/50000000000000 : ℝ)^79 := by
    have hnat : (1861208517 : ℕ)^95*50000000000000^79 ≤ 6620265726177^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861208517 10000000000 6620265726177 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156016797/312500000 : ℝ), (1248445211/2500000000 : ℝ), (1861208517/10000000000 : ℝ)] ![(21686619719101/50000000000000 : ℝ), (1355819659423/3125000000000 : ℝ), (6620265726177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156016797/312500000 : ℝ)|^95 ≤ (21686619719101/50000000000000 : ℝ)^79
        have hw : |(156016797/312500000 : ℝ)|=(156016797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248445211/2500000000 : ℝ)|^95 ≤ (1355819659423/3125000000000 : ℝ)^79
        have hw : |(1248445211/2500000000 : ℝ)|=(1248445211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1861208517/10000000000 : ℝ)|^95 ≤ (6620265726177/50000000000000 : ℝ)^79
        have hw : |(1861208517/10000000000 : ℝ)|=(1861208517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329062_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5364211951/10000000000 : ℝ)*x 0 + (2682639111/5000000000 : ℝ)*x 1 + (-885419757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364211951/10000000000 : ℝ)^95 ≤ (47284883149487/100000000000000 : ℝ)^79 := by
    have hnat : (5364211951 : ℕ)^95*100000000000000^79 ≤ 47284883149487^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364211951 10000000000 47284883149487 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2682639111/5000000000 : ℝ)^95 ≤ (5912023254099/12500000000000 : ℝ)^79 := by
    have hnat : (2682639111 : ℕ)^95*12500000000000^79 ≤ 5912023254099^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682639111 5000000000 5912023254099 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885419757/10000000000 : ℝ)^95 ≤ (5418930800473/100000000000000 : ℝ)^79 := by
    have hnat : (885419757 : ℕ)^95*100000000000000^79 ≤ 5418930800473^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885419757 10000000000 5418930800473 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364211951/10000000000 : ℝ), (2682639111/5000000000 : ℝ), (-885419757/10000000000 : ℝ)] ![(47284883149487/100000000000000 : ℝ), (5912023254099/12500000000000 : ℝ), (5418930800473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364211951/10000000000 : ℝ)|^95 ≤ (47284883149487/100000000000000 : ℝ)^79
        have hw : |(5364211951/10000000000 : ℝ)|=(5364211951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2682639111/5000000000 : ℝ)|^95 ≤ (5912023254099/12500000000000 : ℝ)^79
        have hw : |(2682639111/5000000000 : ℝ)|=(2682639111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-885419757/10000000000 : ℝ)|^95 ≤ (5418930800473/100000000000000 : ℝ)^79
        have hw : |(-885419757/10000000000 : ℝ)|=(885419757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329062 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-23904211/500000000 : ℝ)*X 0 0+(205616203/400000000 : ℝ)*X 0 1+(-182853893/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5140404937/10000000000 : ℝ)*X 1 0+(-59760511/1250000000 : ℝ)*X 1 1+(-5851324791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2570202701/5000000000 : ℝ)*X 2 0+(339471177/625000000 : ℝ)*X 2 1+(1105617613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-14188211/80000000 : ℝ)*X 0 0+(704380793/5000000000 : ℝ)*X 0 1+(-4068126191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1242751437/5000000000 : ℝ)*X 1 0+(-573997173/10000000000 : ℝ)*X 1 1+(-2034063347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2485503283/10000000000 : ℝ)*X 2 0+(7564580463/10000000000 : ℝ)*X 2 1+(1444661711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3660355173/10000000000 : ℝ)*X 0 0+(7445211297/10000000000 : ℝ)*X 0 1+(-1057971/5000000000 : ℝ)*X 0 2+(3660355173/10000000000 : ℝ)*X 1 0+(7445211297/10000000000 : ℝ)*X 1 1+(-1057971/5000000000 : ℝ)*X 1 2+(3660355173/10000000000 : ℝ)*X 2 0+(7445211297/10000000000 : ℝ)*X 2 1+(-1057971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-10579217/200000000 : ℝ)*X 0 0+(604215889/2500000000 : ℝ)*X 0 1+(-4108058133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1284031863/10000000000 : ℝ)*X 1 0+(-1782637979/10000000000 : ℝ)*X 1 1+(-4108058333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7252870449/10000000000 : ℝ)*X 2 0+(2854863387/10000000000 : ℝ)*X 2 1+(1460454149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7833438661/10000000000 : ℝ)*X 0 0+(3203501647/10000000000 : ℝ)*X 0 1+(-658977/2000000000 : ℝ)*X 0 2+(7833438661/10000000000 : ℝ)*X 1 0+(3203501647/10000000000 : ℝ)*X 1 1+(-658977/2000000000 : ℝ)*X 1 2+(7833438661/10000000000 : ℝ)*X 2 0+(3203501647/10000000000 : ℝ)*X 2 1+(-658977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1185017/10000000000 : ℝ)*X 0 0+(3318615233/5000000000 : ℝ)*X 0 1+(-912354437/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((7392147821/10000000000 : ℝ)*X 1 0+(-151221139/2000000000 : ℝ)*X 1 1+(-1630286501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1634940011/10000000000 : ℝ)*X 2 0+(3510164687/5000000000 : ℝ)*X 2 1+(745035533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8185148359/10000000000 : ℝ)*X 0 0+(81478787/312500000 : ℝ)*X 0 1+(-311527203/10000000000 : ℝ)*X 0 2+(8185148359/10000000000 : ℝ)*X 1 0+(81478787/312500000 : ℝ)*X 1 1+(-311527203/10000000000 : ℝ)*X 1 2+(8185148359/10000000000 : ℝ)*X 2 0+(81478787/312500000 : ℝ)*X 2 1+(-311527203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((60447/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60447/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64623070399324562200449/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121495020569/100000000000 : ℝ)*(base7) + (31547/500000000000 : ℝ)*(base23) + (105163/1000000000000 : ℝ)*(base39) + (1454393/1000000000000 : ℝ)*(base60) + (1539530204083/1000000000000 : ℝ)*(major_s0_0) + (1539530204083/1000000000000 : ℝ)*(major_s0_1) + (1539530204083/1000000000000 : ℝ)*(major_s0_2) + (2952609/500000000000 : ℝ)*(sp_s0_0) + (355423/62500000000 : ℝ)*(sp_s0_1) + (173762285429/100000000000 : ℝ)*(sp_s0_7) + (54302011837/31250000000 : ℝ)*(sp_s0_8) + (1737670002459/1000000000000 : ℝ)*(sp_s0_9) + (1907321989713/1000000000000 : ℝ)*(sp_s0_13) + (10326511/250000000000 : ℝ)*(sp_s0_14) + (86546473003/125000000000 : ℝ)*(f.failure) + (108604379097/62500000000 : ℝ)*(f.sum) + (2213368197161531/5000000000000000000000000000 : ℝ)*base63 + (6249001778233483/10000000000000000000000000000 : ℝ)*base64 + (3297276434766517/10000000000000000000000000000 : ℝ)*base67 + (1646433635661531/10000000000000000000000000000 : ℝ)*base69 + (256943186973247/625000000000000000000000000 : ℝ)*base70 + (6257694062766517/10000000000000000000000000000 : ℝ)*base73 + (5456740429338469/10000000000000000000000000000 : ℝ)*base74 + (10620578461338469/10000000000000000000000000000 : ℝ)*base76 + (768082385266517/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (549/390625000000000 : ℝ)*base87 + (549/390625000000000 : ℝ)*base89 + (549/390625000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30119/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30119/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1525923614730221127147/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207718628851/1000000000000 : ℝ)*(base7) + (2753193197/500000000000 : ℝ)*(base60) + (745452305439/500000000000 : ℝ)*(major_s0_0) + (745452305439/500000000000 : ℝ)*(major_s0_1) + (745452305439/500000000000 : ℝ)*(major_s0_2) + (4496761/1000000000000 : ℝ)*(sp_s0_0) + (3754809/1000000000000 : ℝ)*(sp_s0_1) + (521223/500000000000 : ℝ)*(sp_s0_7) + (979907/31250000000 : ℝ)*(sp_s0_8) + (833072890533/500000000000 : ℝ)*(sp_s0_14) + (41652905211/25000000000 : ℝ)*(sp_s0_15) + (1666151320273/1000000000000 : ℝ)*(sp_s0_16) + (37564338083/20000000000 : ℝ)*(sp_s0_20) + (515653/100000000000 : ℝ)*(sp_s0_27) + (670503431829/1000000000000 : ℝ)*(f.failure) + (1666151320273/1000000000000 : ℝ)*(f.sum) + (317043066380423/2500000000000000000000000000 : ℝ)*base63 + (2579358290035639/5000000000000000000000000000 : ℝ)*base64 + (2083202360464361/5000000000000000000000000000 : ℝ)*base67 + (1520550345619577/5000000000000000000000000000 : ℝ)*base68 + (11929684103451/312500000000000000000000000 : ℝ)*base70 + (2492654363964361/5000000000000000000000000000 : ℝ)*base73 + (1857355269619577/5000000000000000000000000000 : ℝ)*base74 + (2349515881619577/5000000000000000000000000000 : ℝ)*base76 + (218915025785639/2500000000000000000000000000 : ℝ)*base78 + (7719/25000000000000000 : ℝ)*base86 + (7719/25000000000000000 : ℝ)*base88 + (7719/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50613/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50613/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (337866423034475649243/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1015736800827/1000000000000 : ℝ)*(base7) + (92479/100000000000 : ℝ)*(base11) + (412359/1000000000000 : ℝ)*(base15) + (56502813953/250000000000 : ℝ)*(base39) + (749569/1000000000000 : ℝ)*(base50) + (183802712391/125000000000 : ℝ)*(major_s0_0) + (183802712391/125000000000 : ℝ)*(major_s0_1) + (183802712391/125000000000 : ℝ)*(major_s0_2) + (180333/1000000000000 : ℝ)*(sp_s0_2) + (448173/31250000000 : ℝ)*(sp_s0_9) + (868476461619/500000000000 : ℝ)*(sp_s0_21) + (434238358917/250000000000 : ℝ)*(sp_s0_22) + (868469663079/500000000000 : ℝ)*(sp_s0_23) + (1677028467851/1000000000000 : ℝ)*(sp_s0_27) + (41330729189/62500000000 : ℝ)*(f.failure) + (434238462007/250000000000 : ℝ)*(f.sum) + (143993403186387/625000000000000000000000000 : ℝ)*base63 + (18567016123809/1250000000000000000000000000 : ℝ)*base65 + (664656699501191/1250000000000000000000000000 : ℝ)*base66 + (1239406502498887/1250000000000000000000000000 : ℝ)*base69 + (269314484231/78125000000000000000000000 : ℝ)*base71 + (830144161251191/1250000000000000000000000000 : ℝ)*base72 + (869175269498887/1250000000000000000000000000 : ℝ)*base75 + (1000701882123887/1250000000000000000000000000 : ℝ)*base77 + (196978130376191/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (179/1562500000000000 : ℝ)*base86 + (179/1562500000000000 : ℝ)*base88 + (179/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (60447/100000 : ℝ) ^ (93/16 : ℝ) ≤ (1340234373521634319/25000000000000000000 : ℝ) := by
    have hpowers : (60447/100000 : ℝ)^93 ≤ (1340234373521634319/25000000000000000000 : ℝ)^16 := by
      have hnat : (60447 : ℕ)^93*25000000000000000000^16 ≤ 1340234373521634319^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60447 100000 1340234373521634319 25000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60447/100000 : ℝ)) (X := (1340234373521634319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (26340234373521634319/25000000000000000000 : ℝ) ≤ (10090248712136323/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26340234373521634319/25000000000000000000 : ℝ)^16 ≤ (10090248712136323/10000000000000000 : ℝ)^93 := by
      have hnat : (26340234373521634319 : ℕ)^16*10000000000000000^93 ≤ 10090248712136323^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26340234373521634319 25000000000000000000 10090248712136323 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10090248712136323/10000000000000000 : ℝ)) (X := (26340234373521634319/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13840234373521634319/12500000000000000000 : ℝ) ≤ (5088386094206023/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (13840234373521634319/12500000000000000000 : ℝ)^16 ≤ (5088386094206023/5000000000000000 : ℝ)^93 := by
      have hnat : (13840234373521634319 : ℕ)^16*5000000000000000^93 ≤ 5088386094206023^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13840234373521634319 12500000000000000000 5088386094206023 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5088386094206023/5000000000000000 : ℝ)) (X := (13840234373521634319/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(30082904045441/2014900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86523476275723/6044700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60447/100000 : ℝ)) (alpha := (30082904045441/2014900000000000 : ℝ)) (beta := (86523476275723/6044700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60447/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(30082904045441/2014900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86523476275723/6044700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30119/50000 : ℝ) ^ (93/16 : ℝ) ≤ (1050818072783600157/20000000000000000000 : ℝ) := by
    have hpowers : (30119/50000 : ℝ)^93 ≤ (1050818072783600157/20000000000000000000 : ℝ)^16 := by
      have hnat : (30119 : ℕ)^93*20000000000000000000^16 ≤ 1050818072783600157^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30119 50000 1050818072783600157 20000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30119/50000 : ℝ)) (X := (1050818072783600157/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (21050818072783600157/20000000000000000000 : ℝ) ≤ (1261060941114077/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (21050818072783600157/20000000000000000000 : ℝ)^16 ≤ (1261060941114077/1250000000000000 : ℝ)^93 := by
      have hnat : (21050818072783600157 : ℕ)^16*1250000000000000^93 ≤ 1261060941114077^93*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21050818072783600157 20000000000000000000 1261060941114077 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261060941114077/1250000000000000 : ℝ)) (X := (21050818072783600157/20000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11050818072783600157/10000000000000000000 : ℝ) ≤ (158959224106393/156250000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (11050818072783600157/10000000000000000000 : ℝ)^16 ≤ (158959224106393/156250000000000 : ℝ)^93 := by
      have hnat : (11050818072783600157 : ℕ)^16*156250000000000^93 ≤ 158959224106393^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11050818072783600157 10000000000000000000 158959224106393 156250000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (158959224106393/156250000000000 : ℝ)) (X := (11050818072783600157/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(11060941114077/752975000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10612851737067/752975000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (30119/50000 : ℝ)) (alpha := (11060941114077/752975000000000 : ℝ)) (beta := (10612851737067/752975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30119/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(11060941114077/752975000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10612851737067/752975000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (50613/100000 : ℝ) ^ (93/16 : ℝ) ≤ (381991180990314947/20000000000000000000 : ℝ) := by
    have hpowers : (50613/100000 : ℝ)^93 ≤ (381991180990314947/20000000000000000000 : ℝ)^16 := by
      have hnat : (50613 : ℕ)^93*20000000000000000000^16 ≤ 381991180990314947^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50613 100000 381991180990314947 20000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50613/100000 : ℝ)) (X := (381991180990314947/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20381991180990314947/20000000000000000000 : ℝ) ≤ (10032602626454519/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (20381991180990314947/20000000000000000000 : ℝ)^16 ≤ (10032602626454519/10000000000000000 : ℝ)^93 := by
      have hnat : (20381991180990314947 : ℕ)^16*10000000000000000^93 ≤ 10032602626454519^93*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20381991180990314947 20000000000000000000 10032602626454519 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032602626454519/10000000000000000 : ℝ)) (X := (20381991180990314947/20000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10381991180990314947/10000000000000000000 : ℝ) ≤ (5032351606871869/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10381991180990314947/10000000000000000000 : ℝ)^16 ≤ (5032351606871869/5000000000000000 : ℝ)^93 := by
      have hnat : (10381991180990314947 : ℕ)^16*5000000000000000^93 ≤ 5032351606871869^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10381991180990314947 10000000000000000000 5032351606871869 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032351606871869/5000000000000000 : ℝ)) (X := (10381991180990314947/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(32602626454519/5061300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(10700195763073/1687100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (50613/100000 : ℝ)) (alpha := (32602626454519/5061300000000000 : ℝ)) (beta := (10700195763073/1687100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (50613/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(32602626454519/5061300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(10700195763073/1687100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1420815249/10000000000 : ℝ)*X 0 0+(1234586697/2500000000 : ℝ)*X 0 1+(-5396047183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4939296599/10000000000 : ℝ)*X 1 0+(-355053049/2500000000 : ℝ)*X 1 1+(-1079114893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((156016797/312500000 : ℝ)*X 2 0+(1248445211/2500000000 : ℝ)*X 2 1+(1861208517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5364211951/10000000000 : ℝ)*X 0 0+(2682639111/5000000000 : ℝ)*X 0 1+(-885419757/10000000000 : ℝ)*X 0 2+(5364211951/10000000000 : ℝ)*X 1 0+(2682639111/5000000000 : ℝ)*X 1 1+(-885419757/10000000000 : ℝ)*X 1 2+(5364211951/10000000000 : ℝ)*X 2 0+(2682639111/5000000000 : ℝ)*X 2 1+(-885419757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329062_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-1058067250762847538530122317093308083/102384654897010000000000000000000000 : ℝ) := by norm_num
    linear_combination (71/62500000000 : ℝ)*(base7) + (123/40000000000 : ℝ)*(base21) + (531/200000000000 : ℝ)*(base27) + (24455201017/100000000000 : ℝ)*(base39) + (61219244419/250000000000 : ℝ)*(base49) + (773/50000000000 : ℝ)*(base53) + (55589/25000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (111177999227/50000000000 : ℝ)*(major_s1_2) + (3444745518733/1000000000000 : ℝ)*(sp_s1_0) + (3444745513703/1000000000000 : ℝ)*(sp_s1_1) + (137789821099/40000000000 : ℝ)*(sp_s1_2) + (999999998481/1000000000000 : ℝ)*(sp_s1_6) + (3444745529163/1000000000000 : ℝ)*(f.sum) + (207837980206285879/952758091875000000000000000000 : ℝ)*base62 + (4217980477117/21088750000000000000000000 : ℝ)*base65 + (23669944709720351/4706093750000000000000000 : ℝ)*base67 + (28173019278019/253065000000000000000000000 : ℝ)*base68 + (12526820805104521/424917223750000000000000000000 : ℝ)*base70 + (90138653568409/151117500000000000000000000 : ℝ)*base72 + (61065891220889/301190000000000000000000000 : ℝ)*base74 + (15696942511309/100745000000000000000000000 : ℝ)*base76 + (12625026888033547728697/9103015965000000000000000000000 : ℝ)*base78 + (503/100000000000 : ℝ)*base81 + (1387/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c329064_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2874637707/10000000000 : ℝ)*x 0 + (-1747350133/5000000000 : ℝ)*x 1 + (-556519/1000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2874637707/10000000000 : ℝ)^95 ≤ (11166037196791/50000000000000 : ℝ)^79 := by
    have hnat : (2874637707 : ℕ)^95*50000000000000^79 ≤ 11166037196791^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2874637707 10000000000 11166037196791 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1747350133/5000000000 : ℝ)^95 ≤ (7061159215423/25000000000000 : ℝ)^79 := by
    have hnat : (1747350133 : ℕ)^95*25000000000000^79 ≤ 7061159215423^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747350133 5000000000 7061159215423 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556519/1000000 : ℝ)^95 ≤ (49423288725267/100000000000000 : ℝ)^79 := by
    have hnat : (556519 : ℕ)^95*100000000000000^79 ≤ 49423288725267^79*1000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556519 1000000 49423288725267 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2874637707/10000000000 : ℝ), (-1747350133/5000000000 : ℝ), (-556519/1000000 : ℝ)] ![(11166037196791/50000000000000 : ℝ), (7061159215423/25000000000000 : ℝ), (49423288725267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2874637707/10000000000 : ℝ)|^95 ≤ (11166037196791/50000000000000 : ℝ)^79
        have hw : |(-2874637707/10000000000 : ℝ)|=(2874637707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1747350133/5000000000 : ℝ)|^95 ≤ (7061159215423/25000000000000 : ℝ)^79
        have hw : |(-1747350133/5000000000 : ℝ)|=(1747350133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556519/1000000 : ℝ)|^95 ≤ (49423288725267/100000000000000 : ℝ)^79
        have hw : |(-556519/1000000 : ℝ)|=(556519/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329064_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3319941771/10000000000 : ℝ)*x 0 + (1292202773/2500000000 : ℝ)*x 1 + (-218284831/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3319941771/10000000000 : ℝ)^95 ≤ (5310974640027/20000000000000 : ℝ)^79 := by
    have hnat : (3319941771 : ℕ)^95*20000000000000^79 ≤ 5310974640027^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319941771 10000000000 5310974640027 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292202773/2500000000 : ℝ)^95 ≤ (45221316208871/100000000000000 : ℝ)^79 := by
    have hnat : (1292202773 : ℕ)^95*100000000000000^79 ≤ 45221316208871^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292202773 2500000000 45221316208871 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218284831/625000000 : ℝ)^95 ≤ (7055952645529/25000000000000 : ℝ)^79 := by
    have hnat : (218284831 : ℕ)^95*25000000000000^79 ≤ 7055952645529^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218284831 625000000 7055952645529 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3319941771/10000000000 : ℝ), (1292202773/2500000000 : ℝ), (-218284831/625000000 : ℝ)] ![(5310974640027/20000000000000 : ℝ), (45221316208871/100000000000000 : ℝ), (7055952645529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3319941771/10000000000 : ℝ)|^95 ≤ (5310974640027/20000000000000 : ℝ)^79
        have hw : |(3319941771/10000000000 : ℝ)|=(3319941771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292202773/2500000000 : ℝ)|^95 ≤ (45221316208871/100000000000000 : ℝ)^79
        have hw : |(1292202773/2500000000 : ℝ)|=(1292202773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218284831/625000000 : ℝ)|^95 ≤ (7055952645529/25000000000000 : ℝ)^79
        have hw : |(-218284831/625000000 : ℝ)|=(218284831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329064_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6106267369/10000000000 : ℝ)*x 0 + (-3422961329/10000000000 : ℝ)*x 1 + (1156444717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6106267369/10000000000 : ℝ)^95 ≤ (27628585079069/50000000000000 : ℝ)^79 := by
    have hnat : (6106267369 : ℕ)^95*50000000000000^79 ≤ 27628585079069^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6106267369 10000000000 27628585079069 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3422961329/10000000000 : ℝ)^95 ≤ (27548861910103/100000000000000 : ℝ)^79 := by
    have hnat : (3422961329 : ℕ)^95*100000000000000^79 ≤ 27548861910103^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422961329 10000000000 27548861910103 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1156444717/5000000000 : ℝ)^95 ≤ (8596983959037/50000000000000 : ℝ)^79 := by
    have hnat : (1156444717 : ℕ)^95*50000000000000^79 ≤ 8596983959037^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156444717 5000000000 8596983959037 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6106267369/10000000000 : ℝ), (-3422961329/10000000000 : ℝ), (1156444717/5000000000 : ℝ)] ![(27628585079069/50000000000000 : ℝ), (27548861910103/100000000000000 : ℝ), (8596983959037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6106267369/10000000000 : ℝ)|^95 ≤ (27628585079069/50000000000000 : ℝ)^79
        have hw : |(6106267369/10000000000 : ℝ)|=(6106267369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3422961329/10000000000 : ℝ)|^95 ≤ (27548861910103/100000000000000 : ℝ)^79
        have hw : |(-3422961329/10000000000 : ℝ)|=(3422961329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1156444717/5000000000 : ℝ)|^95 ≤ (8596983959037/50000000000000 : ℝ)^79
        have hw : |(1156444717/5000000000 : ℝ)|=(1156444717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329064 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2874637707/10000000000 : ℝ)*X 0 0+(-1747350133/5000000000 : ℝ)*X 0 1+(-556519/1000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3319941771/10000000000 : ℝ)*X 1 0+(1292202773/2500000000 : ℝ)*X 1 1+(-218284831/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6106267369/10000000000 : ℝ)*X 2 0+(-3422961329/10000000000 : ℝ)*X 2 1+(1156444717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-12857343042210657595274335803/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1156486624167/1000000000000 : ℝ)*(base1) + (39121670873/250000000000 : ℝ)*(base7) + (146161/1000000000000 : ℝ)*(base21) + (75807/250000000000 : ℝ)*(base33) + (1671243185369/1000000000000 : ℝ)*(base39) + (398474377607/500000000000 : ℝ)*(base40) + (14831/250000000000 : ℝ)*(base44) + (62829/1000000000000 : ℝ)*(base50) + (415704401457/500000000000 : ℝ)*(base60) + (555889924193/250000000000 : ℝ)*(major_s0_0) + (555889985169/250000000000 : ℝ)*(major_s0_1) + (55589/25000 : ℝ)*(major_s0_2) + (2250758906981/500000000000 : ℝ)*(sp_s0_0) + (1672515413621/500000000000 : ℝ)*(sp_s0_1) + (669006148081/200000000000 : ℝ)*(sp_s0_2) + (1672515594897/500000000000 : ℝ)*(f.sum) + (2111952557029369/2500000000000000000000000000 : ℝ)*base63 + (1979463637/2500000000000000000000 : ℝ)*base64 + (1101857165953033/2500000000000000000000000000 : ℝ)*base66 + (1746157749/5000000000000000000000 : ℝ)*base69 + (2184713346796199/2500000000000000000000000000 : ℝ)*base70 + (156565163248407/2500000000000000000000000000 : ℝ)*base73 + (1804339892279369/2500000000000000000000000000 : ℝ)*base75 + (2785729609546199/2500000000000000000000000000 : ℝ)*base76 + (480998301602313/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b031 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=62 ∨ c=63 ∨ c=64 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c329062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c329064 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
