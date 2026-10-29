-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1366_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:30.430978+00:00
-- url     : https://prove2.me/submissions/833c9064-35ac-4584-b11b-433108243c15

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1366_s0_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1795042793/10000000000 : ℝ)*x 0 + (5986615507/10000000000 : ℝ)*x 1 + (4816602861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795042793/10000000000 : ℝ)^2163 ≤ (2634463359327/25000000000000 : ℝ)^1651 := by
    have hnat : (1795042793 : ℕ)^2163*25000000000000^1651 ≤ 2634463359327^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795042793 10000000000 2634463359327 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5986615507/10000000000 : ℝ)^2163 ≤ (12765033419519/25000000000000 : ℝ)^1651 := by
    have hnat : (5986615507 : ℕ)^2163*25000000000000^1651 ≤ 12765033419519^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986615507 10000000000 12765033419519 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4816602861/10000000000 : ℝ)^2163 ≤ (38402012861737/100000000000000 : ℝ)^1651 := by
    have hnat : (4816602861 : ℕ)^2163*100000000000000^1651 ≤ 38402012861737^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816602861 10000000000 38402012861737 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1795042793/10000000000 : ℝ), (5986615507/10000000000 : ℝ), (4816602861/10000000000 : ℝ)] ![(2634463359327/25000000000000 : ℝ), (12765033419519/25000000000000 : ℝ), (38402012861737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1795042793/10000000000 : ℝ)|^2163 ≤ (2634463359327/25000000000000 : ℝ)^1651
        have hw : |(-1795042793/10000000000 : ℝ)|=(1795042793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5986615507/10000000000 : ℝ)|^2163 ≤ (12765033419519/25000000000000 : ℝ)^1651
        have hw : |(5986615507/10000000000 : ℝ)|=(5986615507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4816602861/10000000000 : ℝ)|^2163 ≤ (38402012861737/100000000000000 : ℝ)^1651
        have hw : |(4816602861/10000000000 : ℝ)|=(4816602861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8798603/16000000 : ℝ)*x 0 + (-2458921037/10000000000 : ℝ)*x 1 + (1204150851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8798603/16000000 : ℝ)^2163 ≤ (45683031070499/100000000000000 : ℝ)^1651 := by
    have hnat : (8798603 : ℕ)^2163*100000000000000^1651 ≤ 45683031070499^1651*16000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8798603 16000000 45683031070499 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458921037/10000000000 : ℝ)^2163 ≤ (15914950380281/100000000000000 : ℝ)^1651 := by
    have hnat : (2458921037 : ℕ)^2163*100000000000000^1651 ≤ 15914950380281^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458921037 10000000000 15914950380281 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204150851/2500000000 : ℝ)^2163 ≤ (38402018533557/100000000000000 : ℝ)^1651 := by
    have hnat : (1204150851 : ℕ)^2163*100000000000000^1651 ≤ 38402018533557^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204150851 2500000000 38402018533557 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8798603/16000000 : ℝ), (-2458921037/10000000000 : ℝ), (1204150851/2500000000 : ℝ)] ![(45683031070499/100000000000000 : ℝ), (15914950380281/100000000000000 : ℝ), (38402018533557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8798603/16000000 : ℝ)|^2163 ≤ (45683031070499/100000000000000 : ℝ)^1651
        have hw : |(8798603/16000000 : ℝ)|=(8798603/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2458921037/10000000000 : ℝ)|^2163 ≤ (15914950380281/100000000000000 : ℝ)^1651
        have hw : |(-2458921037/10000000000 : ℝ)|=(2458921037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204150851/2500000000 : ℝ)|^2163 ≤ (38402018533557/100000000000000 : ℝ)^1651
        have hw : |(1204150851/2500000000 : ℝ)|=(1204150851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5499126759/10000000000 : ℝ)*x 0 + (4816602819/10000000000 : ℝ)*x 1 + (-2458921907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5499126759/10000000000 : ℝ)^2163 ≤ (45683029808007/100000000000000 : ℝ)^1651 := by
    have hnat : (5499126759 : ℕ)^2163*100000000000000^1651 ≤ 45683029808007^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499126759 10000000000 45683029808007 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4816602819/10000000000 : ℝ)^2163 ≤ (38402012423033/100000000000000 : ℝ)^1651 := by
    have hnat : (4816602819 : ℕ)^2163*100000000000000^1651 ≤ 38402012423033^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816602819 10000000000 38402012423033 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2458921907/10000000000 : ℝ)^2163 ≤ (3182991551489/20000000000000 : ℝ)^1651 := by
    have hnat : (2458921907 : ℕ)^2163*20000000000000^1651 ≤ 3182991551489^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458921907 10000000000 3182991551489 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5499126759/10000000000 : ℝ), (4816602819/10000000000 : ℝ), (-2458921907/10000000000 : ℝ)] ![(45683029808007/100000000000000 : ℝ), (38402012423033/100000000000000 : ℝ), (3182991551489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5499126759/10000000000 : ℝ)|^2163 ≤ (45683029808007/100000000000000 : ℝ)^1651
        have hw : |(5499126759/10000000000 : ℝ)|=(5499126759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4816602819/10000000000 : ℝ)|^2163 ≤ (38402012423033/100000000000000 : ℝ)^1651
        have hw : |(4816602819/10000000000 : ℝ)|=(4816602819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2458921907/10000000000 : ℝ)|^2163 ≤ (3182991551489/20000000000000 : ℝ)^1651
        have hw : |(-2458921907/10000000000 : ℝ)|=(2458921907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2087588061/5000000000 : ℝ)*x 0 + (3105461319/10000000000 : ℝ)*x 1 + (1394571043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087588061/5000000000 : ℝ)^2163 ≤ (99515414533/312500000000 : ℝ)^1651 := by
    have hnat : (2087588061 : ℕ)^2163*312500000000^1651 ≤ 99515414533^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087588061 5000000000 99515414533 312500000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105461319/10000000000 : ℝ)^2163 ≤ (21608607229807/100000000000000 : ℝ)^1651 := by
    have hnat : (3105461319 : ℕ)^2163*100000000000000^1651 ≤ 21608607229807^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105461319 10000000000 21608607229807 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394571043/2500000000 : ℝ)^2163 ≤ (46546460103219/100000000000000 : ℝ)^1651 := by
    have hnat : (1394571043 : ℕ)^2163*100000000000000^1651 ≤ 46546460103219^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394571043 2500000000 46546460103219 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087588061/5000000000 : ℝ), (3105461319/10000000000 : ℝ), (1394571043/2500000000 : ℝ)] ![(99515414533/312500000000 : ℝ), (21608607229807/100000000000000 : ℝ), (46546460103219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087588061/5000000000 : ℝ)|^2163 ≤ (99515414533/312500000000 : ℝ)^1651
        have hw : |(2087588061/5000000000 : ℝ)|=(2087588061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105461319/10000000000 : ℝ)|^2163 ≤ (21608607229807/100000000000000 : ℝ)^1651
        have hw : |(3105461319/10000000000 : ℝ)|=(3105461319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394571043/2500000000 : ℝ)|^2163 ≤ (46546460103219/100000000000000 : ℝ)^1651
        have hw : |(1394571043/2500000000 : ℝ)|=(1394571043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-899687521/5000000000 : ℝ)*x 0 + (2423335747/5000000000 : ℝ)*x 1 + (5955472431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899687521/5000000000 : ℝ)^2163 ≤ (10571185531991/100000000000000 : ℝ)^1651 := by
    have hnat : (899687521 : ℕ)^2163*100000000000000^1651 ≤ 10571185531991^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899687521 5000000000 10571185531991 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423335747/5000000000 : ℝ)^2163 ≤ (38716393551927/100000000000000 : ℝ)^1651 := by
    have hnat : (2423335747 : ℕ)^2163*100000000000000^1651 ≤ 38716393551927^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423335747 5000000000 38716393551927 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5955472431/10000000000 : ℝ)^2163 ≤ (12678105223691/25000000000000 : ℝ)^1651 := by
    have hnat : (5955472431 : ℕ)^2163*25000000000000^1651 ≤ 12678105223691^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5955472431 10000000000 12678105223691 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899687521/5000000000 : ℝ), (2423335747/5000000000 : ℝ), (5955472431/10000000000 : ℝ)] ![(10571185531991/100000000000000 : ℝ), (38716393551927/100000000000000 : ℝ), (12678105223691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899687521/5000000000 : ℝ)|^2163 ≤ (10571185531991/100000000000000 : ℝ)^1651
        have hw : |(-899687521/5000000000 : ℝ)|=(899687521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2423335747/5000000000 : ℝ)|^2163 ≤ (38716393551927/100000000000000 : ℝ)^1651
        have hw : |(2423335747/5000000000 : ℝ)|=(2423335747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5955472431/10000000000 : ℝ)|^2163 ≤ (12678105223691/25000000000000 : ℝ)^1651
        have hw : |(5955472431/10000000000 : ℝ)|=(5955472431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5180114589/10000000000 : ℝ)*x 0 + (-1320054277/10000000000 : ℝ)*x 1 + (5955471473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180114589/10000000000 : ℝ)^2163 ≤ (5280337832019/12500000000000 : ℝ)^1651 := by
    have hnat : (5180114589 : ℕ)^2163*12500000000000^1651 ≤ 5280337832019^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180114589 10000000000 5280337832019 12500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320054277/10000000000 : ℝ)^2163 ≤ (7044887125777/100000000000000 : ℝ)^1651 := by
    have hnat : (1320054277 : ℕ)^2163*100000000000000^1651 ≤ 7044887125777^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320054277 10000000000 7044887125777 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5955471473/10000000000 : ℝ)^2163 ≤ (50712410207339/100000000000000 : ℝ)^1651 := by
    have hnat : (5955471473 : ℕ)^2163*100000000000000^1651 ≤ 50712410207339^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5955471473 10000000000 50712410207339 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180114589/10000000000 : ℝ), (-1320054277/10000000000 : ℝ), (5955471473/10000000000 : ℝ)] ![(5280337832019/12500000000000 : ℝ), (7044887125777/100000000000000 : ℝ), (50712410207339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180114589/10000000000 : ℝ)|^2163 ≤ (5280337832019/12500000000000 : ℝ)^1651
        have hw : |(5180114589/10000000000 : ℝ)|=(5180114589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1320054277/10000000000 : ℝ)|^2163 ≤ (7044887125777/100000000000000 : ℝ)^1651
        have hw : |(-1320054277/10000000000 : ℝ)|=(1320054277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5955471473/10000000000 : ℝ)|^2163 ≤ (50712410207339/100000000000000 : ℝ)^1651
        have hw : |(5955471473/10000000000 : ℝ)|=(5955471473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1036022819/2000000000 : ℝ)*x 0 + (1488868237/2500000000 : ℝ)*x 1 + (-1320052677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036022819/2000000000 : ℝ)^2163 ≤ (42242697378403/100000000000000 : ℝ)^1651 := by
    have hnat : (1036022819 : ℕ)^2163*100000000000000^1651 ≤ 42242697378403^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036022819 2000000000 42242697378403 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1488868237/2500000000 : ℝ)^2163 ≤ (50712426662403/100000000000000 : ℝ)^1651 := by
    have hnat : (1488868237 : ℕ)^2163*100000000000000^1651 ≤ 50712426662403^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488868237 2500000000 50712426662403 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320052677/10000000000 : ℝ)^2163 ≤ (704487593883/10000000000000 : ℝ)^1651 := by
    have hnat : (1320052677 : ℕ)^2163*10000000000000^1651 ≤ 704487593883^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320052677 10000000000 704487593883 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036022819/2000000000 : ℝ), (1488868237/2500000000 : ℝ), (-1320052677/10000000000 : ℝ)] ![(42242697378403/100000000000000 : ℝ), (50712426662403/100000000000000 : ℝ), (704487593883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036022819/2000000000 : ℝ)|^2163 ≤ (42242697378403/100000000000000 : ℝ)^1651
        have hw : |(1036022819/2000000000 : ℝ)|=(1036022819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1488868237/2500000000 : ℝ)|^2163 ≤ (50712426662403/100000000000000 : ℝ)^1651
        have hw : |(1488868237/2500000000 : ℝ)|=(1488868237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1320052677/10000000000 : ℝ)|^2163 ≤ (704487593883/10000000000000 : ℝ)^1651
        have hw : |(-1320052677/10000000000 : ℝ)|=(1320052677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s0_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (523040833/1250000000 : ℝ)*x 0 + (689342037/1250000000 : ℝ)*x 1 + (396410367/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523040833/1250000000 : ℝ)^2163 ≤ (15968200336279/50000000000000 : ℝ)^1651 := by
    have hnat : (523040833 : ℕ)^2163*50000000000000^1651 ≤ 15968200336279^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523040833 1250000000 15968200336279 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689342037/1250000000 : ℝ)^2163 ≤ (9170598344913/20000000000000 : ℝ)^1651 := by
    have hnat : (689342037 : ℕ)^2163*20000000000000^1651 ≤ 9170598344913^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689342037 1250000000 9170598344913 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396410367/1250000000 : ℝ)^2163 ≤ (11105303791451/50000000000000 : ℝ)^1651 := by
    have hnat : (396410367 : ℕ)^2163*50000000000000^1651 ≤ 11105303791451^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396410367 1250000000 11105303791451 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523040833/1250000000 : ℝ), (689342037/1250000000 : ℝ), (396410367/1250000000 : ℝ)] ![(15968200336279/50000000000000 : ℝ), (9170598344913/20000000000000 : ℝ), (11105303791451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523040833/1250000000 : ℝ)|^2163 ≤ (15968200336279/50000000000000 : ℝ)^1651
        have hw : |(523040833/1250000000 : ℝ)|=(523040833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689342037/1250000000 : ℝ)|^2163 ≤ (9170598344913/20000000000000 : ℝ)^1651
        have hw : |(689342037/1250000000 : ℝ)|=(689342037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396410367/1250000000 : ℝ)|^2163 ≤ (11105303791451/50000000000000 : ℝ)^1651
        have hw : |(396410367/1250000000 : ℝ)|=(396410367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (4325/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4325 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4325*1^1024 ≤ 0^1024*1^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4325/1024 : ℝ) ≤ (2085679257262513499/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4325 ≤ (2085679257262513499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4325*100000000000000000000^1024 ≤ 2085679257262513499^1024*5^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2085679257262513499 100000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2085679257262513499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4325 := by
      have hnat : (1 : ℕ)^1024*1^4325 ≤ 1^4325*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102085679257262513499/100000000000000000000 : ℝ) ≤ (10048992877343981/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (102085679257262513499/100000000000000000000 : ℝ)^1024 ≤ (10048992877343981/10000000000000000 : ℝ)^4325 := by
      have hnat : (102085679257262513499 : ℕ)^1024*10000000000000000^4325 ≤ 10048992877343981^4325*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102085679257262513499 100000000000000000000 10048992877343981 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048992877343981/10000000000000000 : ℝ)) (X := (102085679257262513499/100000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52085679257262513499/50000000000000000000 : ℝ) ≤ (5048992877343981/5000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (52085679257262513499/50000000000000000000 : ℝ)^1024 ≤ (5048992877343981/5000000000000000 : ℝ)^4325 := by
      have hnat : (52085679257262513499 : ℕ)^1024*5000000000000000^4325 ≤ 5048992877343981^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52085679257262513499 50000000000000000000 5048992877343981 5000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048992877343981/5000000000000000 : ℝ)) (X := (52085679257262513499/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48992877343981/4000000000000000 : ℝ)*(0 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48992877343981/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2085679257262513499/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48992877343981/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48992877343981/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048992877343981/10000000000000000 : ℝ) by norm_num, show 1+(2085679257262513499/100000000000000000000 : ℝ)+(0 : ℝ)=(102085679257262513499/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2085679257262513499/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48992877343981/4000000000000000 : ℝ)*(2/5 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48992877343981/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048992877343981/5000000000000000 : ℝ) by norm_num, show 1+2*(2085679257262513499/100000000000000000000 : ℝ)=(52085679257262513499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48992877343981/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48992877343981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48992877343981/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48992877343981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48992877343981/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48992877343981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1795042793/10000000000 : ℝ)*X 0 0+(5986615507/10000000000 : ℝ)*X 0 1+(4816602861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8798603/16000000 : ℝ)*X 1 0+(-2458921037/10000000000 : ℝ)*X 1 1+(1204150851/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5499126759/10000000000 : ℝ)*X 2 0+(4816602819/10000000000 : ℝ)*X 2 1+(-2458921907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2087588061/5000000000 : ℝ)*X 0 0+(3105461319/10000000000 : ℝ)*X 0 1+(1394571043/2500000000 : ℝ)*X 0 2+(2087588061/5000000000 : ℝ)*X 1 0+(3105461319/10000000000 : ℝ)*X 1 1+(1394571043/2500000000 : ℝ)*X 1 2+(2087588061/5000000000 : ℝ)*X 2 0+(3105461319/10000000000 : ℝ)*X 2 1+(1394571043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-899687521/5000000000 : ℝ)*X 0 0+(2423335747/5000000000 : ℝ)*X 0 1+(5955472431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180114589/10000000000 : ℝ)*X 1 0+(-1320054277/10000000000 : ℝ)*X 1 1+(5955471473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036022819/2000000000 : ℝ)*X 2 0+(1488868237/2500000000 : ℝ)*X 2 1+(-1320052677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((523040833/1250000000 : ℝ)*X 0 0+(689342037/1250000000 : ℝ)*X 0 1+(396410367/1250000000 : ℝ)*X 0 2+(523040833/1250000000 : ℝ)*X 1 0+(689342037/1250000000 : ℝ)*X 1 1+(396410367/1250000000 : ℝ)*X 1 2+(523040833/1250000000 : ℝ)*X 2 0+(689342037/1250000000 : ℝ)*X 2 1+(396410367/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192251069917225603518651/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163639173/100000000000000 : ℝ)*(base1) + (22839733/100000000000000 : ℝ)*(base16) + (5404977/625000000000 : ℝ)*(base19) + (434803439/50000000000000 : ℝ)*(base23) + (7704771/5000000000000 : ℝ)*(upper3) + (314773844364881/50000000000000 : ℝ)*(major0) + (314773844364881/50000000000000 : ℝ)*(major1) + (314773844364881/50000000000000 : ℝ)*(major2) + (854694708343631/100000000000000 : ℝ)*(sp0) + (427347929421283/50000000000000 : ℝ)*(sp1) + (854695876871741/100000000000000 : ℝ)*(sp2) + (404397002818397/100000000000000 : ℝ)*(sp3) + (2201774161/100000000000000 : ℝ)*(sp4) + (334088987/25000000000000 : ℝ)*(sp7) + (202199251406759/50000000000000 : ℝ)*(f.failure) + (854696746478619/100000000000000 : ℝ)*(f.sum) + (134688837031261/100000000000000000000000000000 : ℝ)*base65 + (1449725772731261/200000000000000000000000000000 : ℝ)*base67 + (687831254331261/200000000000000000000000000000 : ℝ)*base69 + (1029176081931261/200000000000000000000000000000 : ℝ)*base71 + (112939782231261/100000000000000000000000000000 : ℝ)*base73 + (1062569057931261/200000000000000000000000000000 : ℝ)*base75 + (1217284848131261/200000000000000000000000000000 : ℝ)*base77 + (1724068687131261/200000000000000000000000000000 : ℝ)*base79 + (68122560631261/100000000000000000000000000000 : ℝ)*base81 + (31541039/5000000000000000000000 : ℝ)*base90 + (31541039/5000000000000000000000 : ℝ)*base92 + (31541039/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31021943916290971558407/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4272417/2000000000000 : ℝ)*(base19) + (84371849/50000000000000 : ℝ)*(base23) + (90749239/50000000000000 : ℝ)*(base39) + (8691181/100000000000000 : ℝ)*(upper2) + (6335959/6250000000000 : ℝ)*(upper4) + (10755701/20000000000000 : ℝ)*(upper5) + (66429760987551/10000000000000 : ℝ)*(major0) + (66429760987551/10000000000000 : ℝ)*(major1) + (83037178547129/12500000000000 : ℝ)*(major2) + (4348303/625000000000 : ℝ)*(sp2) + (225468587129493/25000000000000 : ℝ)*(sp4) + (450937067448561/50000000000000 : ℝ)*(sp5) + (56367104096517/6250000000000 : ℝ)*(sp6) + (85344117265617/20000000000000 : ℝ)*(sp7) + (85344117265617/20000000000000 : ℝ)*(f.failure) + (18037490600329/2000000000000 : ℝ)*(f.sum) + (14962482375149/200000000000000000000000000000 : ℝ)*base66 + (53875786580549/50000000000000000000000000000 : ℝ)*base67 + (147804986100531/40000000000000000000000000000 : ℝ)*base69 + (38679611919451/50000000000000000000000000000 : ℝ)*base72 + (94981767624851/200000000000000000000000000000 : ℝ)*base73 + (311534155140531/40000000000000000000000000000 : ℝ)*base75 + (160418258219469/40000000000000000000000000000 : ℝ)*base78 + (366984000340531/40000000000000000000000000000 : ℝ)*base79 + (37355884660531/20000000000000000000000000000 : ℝ)*base81 + (9541257/2000000000000000000000 : ℝ)*base90 + (9541257/2000000000000000000000 : ℝ)*base92 + (9541257/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1366_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1366_s1_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-988201991/5000000000 : ℝ)*x 0 + (5631522411/10000000000 : ℝ)*x 1 + (631940497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988201991/5000000000 : ℝ)^2163 ≤ (2988520025443/25000000000000 : ℝ)^1651 := by
    have hnat : (988201991 : ℕ)^2163*25000000000000^1651 ≤ 2988520025443^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988201991 5000000000 2988520025443 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5631522411/10000000000 : ℝ)^2163 ≤ (23564657172561/50000000000000 : ℝ)^1651 := by
    have hnat : (5631522411 : ℕ)^2163*50000000000000^1651 ≤ 23564657172561^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631522411 10000000000 23564657172561 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631940497/1250000000 : ℝ)^2163 ≤ (8183321109219/20000000000000 : ℝ)^1651 := by
    have hnat : (631940497 : ℕ)^2163*20000000000000^1651 ≤ 8183321109219^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631940497 1250000000 8183321109219 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988201991/5000000000 : ℝ), (5631522411/10000000000 : ℝ), (631940497/1250000000 : ℝ)] ![(2988520025443/25000000000000 : ℝ), (23564657172561/50000000000000 : ℝ), (8183321109219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988201991/5000000000 : ℝ)|^2163 ≤ (2988520025443/25000000000000 : ℝ)^1651
        have hw : |(-988201991/5000000000 : ℝ)|=(988201991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5631522411/10000000000 : ℝ)|^2163 ≤ (23564657172561/50000000000000 : ℝ)^1651
        have hw : |(5631522411/10000000000 : ℝ)|=(5631522411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631940497/1250000000 : ℝ)|^2163 ≤ (8183321109219/20000000000000 : ℝ)^1651
        have hw : |(631940497/1250000000 : ℝ)|=(631940497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5403223439/10000000000 : ℝ)*x 0 + (-456629687/2000000000 : ℝ)*x 1 + (5055525103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403223439/10000000000 : ℝ)^2163 ≤ (11160523765331/25000000000000 : ℝ)^1651 := by
    have hnat : (5403223439 : ℕ)^2163*25000000000000^1651 ≤ 11160523765331^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403223439 10000000000 11160523765331 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456629687/2000000000 : ℝ)^2163 ≤ (361032185733/2500000000000 : ℝ)^1651 := by
    have hnat : (456629687 : ℕ)^2163*2500000000000^1651 ≤ 361032185733^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456629687 2000000000 361032185733 2500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5055525103/10000000000 : ℝ)^2163 ≤ (8183323499213/20000000000000 : ℝ)^1651 := by
    have hnat : (5055525103 : ℕ)^2163*20000000000000^1651 ≤ 8183323499213^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055525103 10000000000 8183323499213 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403223439/10000000000 : ℝ), (-456629687/2000000000 : ℝ), (5055525103/10000000000 : ℝ)] ![(11160523765331/25000000000000 : ℝ), (361032185733/2500000000000 : ℝ), (8183323499213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403223439/10000000000 : ℝ)|^2163 ≤ (11160523765331/25000000000000 : ℝ)^1651
        have hw : |(5403223439/10000000000 : ℝ)|=(5403223439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456629687/2000000000 : ℝ)|^2163 ≤ (361032185733/2500000000000 : ℝ)^1651
        have hw : |(-456629687/2000000000 : ℝ)|=(456629687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5055525103/10000000000 : ℝ)|^2163 ≤ (8183323499213/20000000000000 : ℝ)^1651
        have hw : |(5055525103/10000000000 : ℝ)|=(5055525103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67540297/125000000 : ℝ)*x 0 + (505552417/1000000000 : ℝ)*x 1 + (-2283149209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67540297/125000000 : ℝ)^2163 ≤ (8928419707187/20000000000000 : ℝ)^1651 := by
    have hnat : (67540297 : ℕ)^2163*20000000000000^1651 ≤ 8928419707187^1651*125000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67540297 125000000 8928419707187 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505552417/1000000000 : ℝ)^2163 ≤ (5114575950393/12500000000000 : ℝ)^1651 := by
    have hnat : (505552417 : ℕ)^2163*12500000000000^1651 ≤ 5114575950393^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505552417 1000000000 5114575950393 12500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283149209/10000000000 : ℝ)^2163 ≤ (722064692161/5000000000000 : ℝ)^1651 := by
    have hnat : (2283149209 : ℕ)^2163*5000000000000^1651 ≤ 722064692161^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283149209 10000000000 722064692161 5000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67540297/125000000 : ℝ), (505552417/1000000000 : ℝ), (-2283149209/10000000000 : ℝ)] ![(8928419707187/20000000000000 : ℝ), (5114575950393/12500000000000 : ℝ), (722064692161/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67540297/125000000 : ℝ)|^2163 ≤ (8928419707187/20000000000000 : ℝ)^1651
        have hw : |(67540297/125000000 : ℝ)|=(67540297/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505552417/1000000000 : ℝ)|^2163 ≤ (5114575950393/12500000000000 : ℝ)^1651
        have hw : |(505552417/1000000000 : ℝ)|=(505552417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283149209/10000000000 : ℝ)|^2163 ≤ (722064692161/5000000000000 : ℝ)^1651
        have hw : |(-2283149209/10000000000 : ℝ)|=(2283149209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214400979/500000000 : ℝ)*x 0 + (3718956841/10000000000 : ℝ)*x 1 + (4936325767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214400979/500000000 : ℝ)^2163 ≤ (16488609741697/50000000000000 : ℝ)^1651 := by
    have hnat : (214400979 : ℕ)^2163*50000000000000^1651 ≤ 16488609741697^1651*500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214400979 500000000 16488609741697 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718956841/10000000000 : ℝ)^2163 ≤ (13682714301207/50000000000000 : ℝ)^1651 := by
    have hnat : (3718956841 : ℕ)^2163*50000000000000^1651 ≤ 13682714301207^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718956841 10000000000 13682714301207 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4936325767/10000000000 : ℝ)^2163 ≤ (1239292246867/3125000000000 : ℝ)^1651 := by
    have hnat : (4936325767 : ℕ)^2163*3125000000000^1651 ≤ 1239292246867^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936325767 10000000000 1239292246867 3125000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214400979/500000000 : ℝ), (3718956841/10000000000 : ℝ), (4936325767/10000000000 : ℝ)] ![(16488609741697/50000000000000 : ℝ), (13682714301207/50000000000000 : ℝ), (1239292246867/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214400979/500000000 : ℝ)|^2163 ≤ (16488609741697/50000000000000 : ℝ)^1651
        have hw : |(214400979/500000000 : ℝ)|=(214400979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3718956841/10000000000 : ℝ)|^2163 ≤ (13682714301207/50000000000000 : ℝ)^1651
        have hw : |(3718956841/10000000000 : ℝ)|=(3718956841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4936325767/10000000000 : ℝ)|^2163 ≤ (1239292246867/3125000000000 : ℝ)^1651
        have hw : |(4936325767/10000000000 : ℝ)|=(4936325767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-98844911/500000000 : ℝ)*x 0 + (2531309513/5000000000 : ℝ)*x 1 + (5624300697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98844911/500000000 : ℝ)^2163 ≤ (186843697569/1562500000000 : ℝ)^1651 := by
    have hnat : (98844911 : ℕ)^2163*1562500000000^1651 ≤ 186843697569^1651*500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98844911 500000000 186843697569 1562500000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2531309513/5000000000 : ℝ)^2163 ≤ (20495926585477/50000000000000 : ℝ)^1651 := by
    have hnat : (2531309513 : ℕ)^2163*50000000000000^1651 ≤ 20495926585477^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531309513 5000000000 20495926585477 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5624300697/10000000000 : ℝ)^2163 ≤ (23525075089069/50000000000000 : ℝ)^1651 := by
    have hnat : (5624300697 : ℕ)^2163*50000000000000^1651 ≤ 23525075089069^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624300697 10000000000 23525075089069 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98844911/500000000 : ℝ), (2531309513/5000000000 : ℝ), (5624300697/10000000000 : ℝ)] ![(186843697569/1562500000000 : ℝ), (20495926585477/50000000000000 : ℝ), (23525075089069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98844911/500000000 : ℝ)|^2163 ≤ (186843697569/1562500000000 : ℝ)^1651
        have hw : |(-98844911/500000000 : ℝ)|=(98844911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2531309513/5000000000 : ℝ)|^2163 ≤ (20495926585477/50000000000000 : ℝ)^1651
        have hw : |(2531309513/5000000000 : ℝ)|=(2531309513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5624300697/10000000000 : ℝ)|^2163 ≤ (23525075089069/50000000000000 : ℝ)^1651
        have hw : |(5624300697/10000000000 : ℝ)|=(5624300697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (10506929/20000000 : ℝ)*x 0 + (-34287453/200000000 : ℝ)*x 1 + (224972031/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10506929/20000000 : ℝ)^2163 ≤ (43028066273821/100000000000000 : ℝ)^1651 := by
    have hnat : (10506929 : ℕ)^2163*100000000000000^1651 ≤ 43028066273821^1651*20000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10506929 20000000 43028066273821 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34287453/200000000 : ℝ)^2163 ≤ (4960891339807/50000000000000 : ℝ)^1651 := by
    have hnat : (34287453 : ℕ)^2163*50000000000000^1651 ≤ 4960891339807^1651*200000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34287453 200000000 4960891339807 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224972031/400000000 : ℝ)^2163 ≤ (47050151033001/100000000000000 : ℝ)^1651 := by
    have hnat : (224972031 : ℕ)^2163*100000000000000^1651 ≤ 47050151033001^1651*400000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224972031 400000000 47050151033001 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10506929/20000000 : ℝ), (-34287453/200000000 : ℝ), (224972031/400000000 : ℝ)] ![(43028066273821/100000000000000 : ℝ), (4960891339807/50000000000000 : ℝ), (47050151033001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10506929/20000000 : ℝ)|^2163 ≤ (43028066273821/100000000000000 : ℝ)^1651
        have hw : |(10506929/20000000 : ℝ)|=(10506929/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34287453/200000000 : ℝ)|^2163 ≤ (4960891339807/50000000000000 : ℝ)^1651
        have hw : |(-34287453/200000000 : ℝ)|=(34287453/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224972031/400000000 : ℝ)|^2163 ≤ (47050151033001/100000000000000 : ℝ)^1651
        have hw : |(224972031/400000000 : ℝ)|=(224972031/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5253464391/10000000000 : ℝ)*x 0 + (562430087/1000000000 : ℝ)*x 1 + (-857186333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253464391/10000000000 : ℝ)^2163 ≤ (43028065104209/100000000000000 : ℝ)^1651 := by
    have hnat : (5253464391 : ℕ)^2163*100000000000000^1651 ≤ 43028065104209^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253464391 10000000000 43028065104209 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562430087/1000000000 : ℝ)^2163 ≤ (2352507603709/5000000000000 : ℝ)^1651 := by
    have hnat : (562430087 : ℕ)^2163*5000000000000^1651 ≤ 2352507603709^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562430087 1000000000 2352507603709 5000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857186333/5000000000 : ℝ)^2163 ≤ (9921782800929/100000000000000 : ℝ)^1651 := by
    have hnat : (857186333 : ℕ)^2163*100000000000000^1651 ≤ 9921782800929^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857186333 5000000000 9921782800929 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253464391/10000000000 : ℝ), (562430087/1000000000 : ℝ), (-857186333/5000000000 : ℝ)] ![(43028065104209/100000000000000 : ℝ), (2352507603709/5000000000000 : ℝ), (9921782800929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253464391/10000000000 : ℝ)|^2163 ≤ (43028065104209/100000000000000 : ℝ)^1651
        have hw : |(5253464391/10000000000 : ℝ)|=(5253464391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562430087/1000000000 : ℝ)|^2163 ≤ (2352507603709/5000000000000 : ℝ)^1651
        have hw : |(562430087/1000000000 : ℝ)|=(562430087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857186333/5000000000 : ℝ)|^2163 ≤ (9921782800929/100000000000000 : ℝ)^1651
        have hw : |(-857186333/5000000000 : ℝ)|=(857186333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s1_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4289064863/10000000000 : ℝ)*x 0 + (49213321/100000000 : ℝ)*x 1 + (933554209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289064863/10000000000 : ℝ)^2163 ≤ (16493875816539/50000000000000 : ℝ)^1651 := by
    have hnat : (4289064863 : ℕ)^2163*50000000000000^1651 ≤ 16493875816539^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289064863 10000000000 16493875816539 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49213321/100000000 : ℝ)^2163 ≤ (19749807650313/50000000000000 : ℝ)^1651 := by
    have hnat : (49213321 : ℕ)^2163*50000000000000^1651 ≤ 19749807650313^1651*100000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49213321 100000000 19749807650313 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933554209/2500000000 : ℝ)^2163 ≤ (13756316523761/50000000000000 : ℝ)^1651 := by
    have hnat : (933554209 : ℕ)^2163*50000000000000^1651 ≤ 13756316523761^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933554209 2500000000 13756316523761 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289064863/10000000000 : ℝ), (49213321/100000000 : ℝ), (933554209/2500000000 : ℝ)] ![(16493875816539/50000000000000 : ℝ), (19749807650313/50000000000000 : ℝ), (13756316523761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289064863/10000000000 : ℝ)|^2163 ≤ (16493875816539/50000000000000 : ℝ)^1651
        have hw : |(4289064863/10000000000 : ℝ)|=(4289064863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49213321/100000000 : ℝ)|^2163 ≤ (19749807650313/50000000000000 : ℝ)^1651
        have hw : |(49213321/100000000 : ℝ)|=(49213321/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933554209/2500000000 : ℝ)|^2163 ≤ (13756316523761/50000000000000 : ℝ)^1651
        have hw : |(933554209/2500000000 : ℝ)|=(933554209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4821/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1593/100000 : ℝ) ^ (4325/1024 : ℝ) ≤ (255164093573/10000000000000000000 : ℝ) := by
    have hpowers : (1593/100000 : ℝ)^4325 ≤ (255164093573/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1593 : ℕ)^4325*10000000000000000000^1024 ≤ 255164093573^1024*100000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1593 100000 255164093573 10000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1593/100000 : ℝ)) (X := (255164093573/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26699/100000 : ℝ) ^ (4325/1024 : ℝ) ≤ (23637713340639119/6250000000000000000 : ℝ) := by
    have hpowers : (26699/100000 : ℝ)^4325 ≤ (23637713340639119/6250000000000000000 : ℝ)^1024 := by
      have hnat : (26699 : ℕ)^4325*6250000000000000000^1024 ≤ 23637713340639119^1024*100000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26699 100000 23637713340639119 6250000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26699/100000 : ℝ)) (X := (23637713340639119/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000255164093573/5000000000000000000 : ℝ) ≤ (5000000060413417/5000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (5000000255164093573/5000000000000000000 : ℝ)^1024 ≤ (5000000060413417/5000000000000000 : ℝ)^4325 := by
      have hnat : (5000000255164093573 : ℕ)^1024*5000000000000000^4325 ≤ 5000000060413417^4325*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000255164093573 5000000000000000000 5000000060413417 5000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000060413417/5000000000000000 : ℝ)) (X := (5000000255164093573/5000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50189102982545580817/50000000000000000000 : ℝ) ≤ (10008941622672791/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50189102982545580817/50000000000000000000 : ℝ)^1024 ≤ (10008941622672791/10000000000000000 : ℝ)^4325 := by
      have hnat : (50189102982545580817 : ℕ)^1024*10000000000000000^4325 ≤ 10008941622672791^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50189102982545580817 50000000000000000000 10008941622672791 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008941622672791/10000000000000000 : ℝ)) (X := (50189102982545580817/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3148637713340639119/3125000000000000000 : ℝ) ≤ (2504470781129687/2500000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (3148637713340639119/3125000000000000000 : ℝ)^1024 ≤ (2504470781129687/2500000000000000 : ℝ)^4325 := by
      have hnat : (3148637713340639119 : ℕ)^1024*2500000000000000^4325 ≤ 2504470781129687^4325*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3148637713340639119 3125000000000000000 2504470781129687 2500000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504470781129687/2500000000000000 : ℝ)) (X := (3148637713340639119/3125000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(255164093573/10000000000000000000 : ℝ) ≤ ((125515757704298637701/125530000000000000000 : ℝ)+2*(8941501845957/2510600000000000 : ℝ)*(1593/100000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (125515757704298637701/125530000000000000000 : ℝ)+2*(8941501845957/2510600000000000 : ℝ)*(1593/100000 : ℝ)=(5000000060413417/5000000000000000 : ℝ) by norm_num, show 1+2*(255164093573/10000000000000000000 : ℝ)=(5000000255164093573/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23637713340639119/6250000000000000000 : ℝ)+(255164093573/10000000000000000000 : ℝ) ≤ ((125515757704298637701/125530000000000000000 : ℝ)+(8941501845957/2510600000000000 : ℝ)*((26699/100000 : ℝ)+(1593/100000 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (125515757704298637701/125530000000000000000 : ℝ)+(8941501845957/2510600000000000 : ℝ)*((26699/100000 : ℝ)+(1593/100000 : ℝ))=(10008941622672791/10000000000000000 : ℝ) by norm_num, show 1+(23637713340639119/6250000000000000000 : ℝ)+(255164093573/10000000000000000000 : ℝ)=(50189102982545580817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23637713340639119/6250000000000000000 : ℝ) ≤ ((125515757704298637701/125530000000000000000 : ℝ)+2*(8941501845957/2510600000000000 : ℝ)*(26699/100000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (125515757704298637701/125530000000000000000 : ℝ)+2*(8941501845957/2510600000000000 : ℝ)*(26699/100000 : ℝ)=(2504470781129687/2500000000000000 : ℝ) by norm_num, show 1+2*(23637713340639119/6250000000000000000 : ℝ)=(3148637713340639119/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125515757704298637701/125530000000000000000 : ℝ)*(X 1 0+X 2 0)+(8941501845957/2510600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (1593/100000 : ℝ)) (hi := (26699/100000 : ℝ)) (c := (125515757704298637701/125530000000000000000 : ℝ)) (alpha := (8941501845957/2510600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125515757704298637701/125530000000000000000 : ℝ)*(X 0 1+X 2 1)+(8941501845957/2510600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (1593/100000 : ℝ)) (hi := (26699/100000 : ℝ)) (c := (125515757704298637701/125530000000000000000 : ℝ)) (alpha := (8941501845957/2510600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125515757704298637701/125530000000000000000 : ℝ)*(X 0 2+X 1 2)+(8941501845957/2510600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (1593/100000 : ℝ)) (hi := (26699/100000 : ℝ)) (c := (125515757704298637701/125530000000000000000 : ℝ)) (alpha := (8941501845957/2510600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-988201991/5000000000 : ℝ)*X 0 0+(5631522411/10000000000 : ℝ)*X 0 1+(631940497/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403223439/10000000000 : ℝ)*X 1 0+(-456629687/2000000000 : ℝ)*X 1 1+(5055525103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67540297/125000000 : ℝ)*X 2 0+(505552417/1000000000 : ℝ)*X 2 1+(-2283149209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214400979/500000000 : ℝ)*X 0 0+(3718956841/10000000000 : ℝ)*X 0 1+(4936325767/10000000000 : ℝ)*X 0 2+(214400979/500000000 : ℝ)*X 1 0+(3718956841/10000000000 : ℝ)*X 1 1+(4936325767/10000000000 : ℝ)*X 1 2+(214400979/500000000 : ℝ)*X 2 0+(3718956841/10000000000 : ℝ)*X 2 1+(4936325767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98844911/500000000 : ℝ)*X 0 0+(2531309513/5000000000 : ℝ)*X 0 1+(5624300697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10506929/20000000 : ℝ)*X 1 0+(-34287453/200000000 : ℝ)*X 1 1+(224972031/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253464391/10000000000 : ℝ)*X 2 0+(562430087/1000000000 : ℝ)*X 2 1+(-857186333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289064863/10000000000 : ℝ)*X 0 0+(49213321/100000000 : ℝ)*X 0 1+(933554209/2500000000 : ℝ)*X 0 2+(4289064863/10000000000 : ℝ)*X 1 0+(49213321/100000000 : ℝ)*X 1 1+(933554209/2500000000 : ℝ)*X 1 2+(4289064863/10000000000 : ℝ)*X 2 0+(49213321/100000000 : ℝ)*X 2 1+(933554209/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1311849564650503089370827/125530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15924211/100000000000000 : ℝ)*(base1) + (349899261/20000000000000 : ℝ)*(base19) + (1852638763/100000000000000 : ℝ)*(base23) + (326304707/100000000000000 : ℝ)*(upper3) + (11850159/50000000000000 : ℝ)*(upper5) + (1278799445957817/100000000000000 : ℝ)*(major0) + (1278799445957817/100000000000000 : ℝ)*(major1) + (1278799445957817/100000000000000 : ℝ)*(major2) + (868065803881559/50000000000000 : ℝ)*(sp0) + (217017826574523/12500000000000 : ℝ)*(sp1) + (69445700378149/4000000000000 : ℝ)*(sp2) + (821448054869899/100000000000000 : ℝ)*(sp3) + (6385126791/50000000000000 : ℝ)*(sp4) + (6110679481/100000000000000 : ℝ)*(sp7) + (102681772684199/12500000000000 : ℝ)*(f.failure) + (1736144362092489/100000000000000 : ℝ)*(f.sum) + (23615924340841/125530000000000000000000000000 : ℝ)*base66 + (3891206841311691283/12553000000000000000000000000000000 : ℝ)*base68 + (30409867257457691283/12553000000000000000000000000000000 : ℝ)*base70 + (9350984115658308717/12553000000000000000000000000000000 : ℝ)*base71 + (29526132647799/125530000000000000000000000000 : ℝ)*base73 + (21963494968347691283/12553000000000000000000000000000000 : ℝ)*base76 + (90823102106786308717/12553000000000000000000000000000000 : ℝ)*base77 + (14185808343828308717/12553000000000000000000000000000000 : ℝ)*base79 + (502643113849851/125530000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8876721/1250000000000000000000 : ℝ)*base89 + (8876721/1250000000000000000000 : ℝ)*base91 + (8876721/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19610660305250342099153130351/3138250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64833987/100000000000000 : ℝ)*(base1) + (633887781/50000000000000 : ℝ)*(base19) + (246156249/20000000000000 : ℝ)*(base23) + (148895973/100000000000000 : ℝ)*(upper3) + (137648029/100000000000000 : ℝ)*(upper5) + (1311373032395783/100000000000000 : ℝ)*(major0) + (1311373032395783/100000000000000 : ℝ)*(major1) + (1311373032395783/100000000000000 : ℝ)*(major2) + (134769043/2000000000000 : ℝ)*(sp1) + (842063389/12500000000000 : ℝ)*(sp2) + (1780367654479499/100000000000000 : ℝ)*(sp4) + (8901797917089/500000000000 : ℝ)*(sp5) + (890179811178577/50000000000000 : ℝ)*(sp6) + (421189101007433/50000000000000 : ℝ)*(sp7) + (842378266848853/100000000000000 : ℝ)*(f.failure) + (222545948705689/12500000000000 : ℝ)*(f.sum) + (21962754512991/125530000000000000000000000000 : ℝ)*base65 + (3728592016298235117/12553000000000000000000000000000000 : ℝ)*base68 + (17164016066336764883/12553000000000000000000000000000000 : ℝ)*base69 + (48772439575099764883/12553000000000000000000000000000000 : ℝ)*base71 + (394832216326169/125530000000000000000000000000 : ℝ)*base74 + (42518494579545764883/12553000000000000000000000000000000 : ℝ)*base75 + (16606124179447764883/12553000000000000000000000000000000 : ℝ)*base77 + (83872856837263764883/12553000000000000000000000000000000 : ℝ)*base79 + (112093868687211/125530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (28165613/10000000000000000000000 : ℝ)*base90 + (28165613/10000000000000000000000 : ℝ)*base92 + (28165613/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1366_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4821/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1366_s2_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-100725493/500000000 : ℝ)*x 0 + (5473357193/10000000000 : ℝ)*x 1 + (518924697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100725493/500000000 : ℝ)^2163 ≤ (12256933593479/100000000000000 : ℝ)^1651 := by
    have hnat : (100725493 : ℕ)^2163*100000000000000^1651 ≤ 12256933593479^1651*500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100725493 500000000 12256933593479 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473357193/10000000000 : ℝ)^2163 ≤ (354709136201/781250000000 : ℝ)^1651 := by
    have hnat : (5473357193 : ℕ)^2163*781250000000^1651 ≤ 354709136201^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473357193 10000000000 354709136201 781250000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518924697/1000000000 : ℝ)^2163 ≤ (42340296955953/100000000000000 : ℝ)^1651 := by
    have hnat : (518924697 : ℕ)^2163*100000000000000^1651 ≤ 42340296955953^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518924697 1000000000 42340296955953 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100725493/500000000 : ℝ), (5473357193/10000000000 : ℝ), (518924697/1000000000 : ℝ)] ![(12256933593479/100000000000000 : ℝ), (354709136201/781250000000 : ℝ), (42340296955953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100725493/500000000 : ℝ)|^2163 ≤ (12256933593479/100000000000000 : ℝ)^1651
        have hw : |(-100725493/500000000 : ℝ)|=(100725493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473357193/10000000000 : ℝ)|^2163 ≤ (354709136201/781250000000 : ℝ)^1651
        have hw : |(5473357193/10000000000 : ℝ)|=(5473357193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518924697/1000000000 : ℝ)|^2163 ≤ (42340296955953/100000000000000 : ℝ)^1651
        have hw : |(518924697/1000000000 : ℝ)|=(518924697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682143581/5000000000 : ℝ)*x 0 + (-2161123851/10000000000 : ℝ)*x 1 + (324327953/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682143581/5000000000 : ℝ)^2163 ≤ (8844221518989/20000000000000 : ℝ)^1651 := by
    have hnat : (2682143581 : ℕ)^2163*20000000000000^1651 ≤ 8844221518989^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682143581 5000000000 8844221518989 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161123851/10000000000 : ℝ)^2163 ≤ (839912028693/6250000000000 : ℝ)^1651 := by
    have hnat : (2161123851 : ℕ)^2163*6250000000000^1651 ≤ 839912028693^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161123851 10000000000 839912028693 6250000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324327953/625000000 : ℝ)^2163 ≤ (8468059985529/20000000000000 : ℝ)^1651 := by
    have hnat : (324327953 : ℕ)^2163*20000000000000^1651 ≤ 8468059985529^1651*625000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324327953 625000000 8468059985529 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682143581/5000000000 : ℝ), (-2161123851/10000000000 : ℝ), (324327953/625000000 : ℝ)] ![(8844221518989/20000000000000 : ℝ), (839912028693/6250000000000 : ℝ), (8468059985529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682143581/5000000000 : ℝ)|^2163 ≤ (8844221518989/20000000000000 : ℝ)^1651
        have hw : |(2682143581/5000000000 : ℝ)|=(2682143581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161123851/10000000000 : ℝ)|^2163 ≤ (839912028693/6250000000000 : ℝ)^1651
        have hw : |(-2161123851/10000000000 : ℝ)|=(2161123851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324327953/625000000 : ℝ)|^2163 ≤ (8468059985529/20000000000000 : ℝ)^1651
        have hw : |(324327953/625000000 : ℝ)|=(324327953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682143593/5000000000 : ℝ)*x 0 + (518924721/1000000000 : ℝ)*x 1 + (-216112387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682143593/5000000000 : ℝ)^2163 ≤ (44221107854147/100000000000000 : ℝ)^1651 := by
    have hnat : (2682143593 : ℕ)^2163*100000000000000^1651 ≤ 44221107854147^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682143593 5000000000 44221107854147 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518924721/1000000000 : ℝ)^2163 ≤ (21170149760721/50000000000000 : ℝ)^1651 := by
    have hnat : (518924721 : ℕ)^2163*50000000000000^1651 ≤ 21170149760721^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518924721 1000000000 21170149760721 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216112387/1000000000 : ℝ)^2163 ≤ (3359648153469/25000000000000 : ℝ)^1651 := by
    have hnat : (216112387 : ℕ)^2163*25000000000000^1651 ≤ 3359648153469^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216112387 1000000000 3359648153469 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682143593/5000000000 : ℝ), (518924721/1000000000 : ℝ), (-216112387/1000000000 : ℝ)] ![(44221107854147/100000000000000 : ℝ), (21170149760721/50000000000000 : ℝ), (3359648153469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682143593/5000000000 : ℝ)|^2163 ≤ (44221107854147/100000000000000 : ℝ)^1651
        have hw : |(2682143593/5000000000 : ℝ)|=(2682143593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518924721/1000000000 : ℝ)|^2163 ≤ (21170149760721/50000000000000 : ℝ)^1651
        have hw : |(518924721/1000000000 : ℝ)|=(518924721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216112387/1000000000 : ℝ)|^2163 ≤ (3359648153469/25000000000000 : ℝ)^1651
        have hw : |(-216112387/1000000000 : ℝ)|=(216112387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314738469/10000000000 : ℝ)*x 0 + (2012070431/5000000000 : ℝ)*x 1 + (2312303789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314738469/10000000000 : ℝ)^2163 ≤ (8311671361979/25000000000000 : ℝ)^1651 := by
    have hnat : (4314738469 : ℕ)^2163*25000000000000^1651 ≤ 8311671361979^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314738469 10000000000 8311671361979 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012070431/5000000000 : ℝ)^2163 ≤ (30344246916237/100000000000000 : ℝ)^1651 := by
    have hnat : (2012070431 : ℕ)^2163*100000000000000^1651 ≤ 30344246916237^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012070431 5000000000 30344246916237 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312303789/5000000000 : ℝ)^2163 ≤ (36409067625597/100000000000000 : ℝ)^1651 := by
    have hnat : (2312303789 : ℕ)^2163*100000000000000^1651 ≤ 36409067625597^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312303789 5000000000 36409067625597 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314738469/10000000000 : ℝ), (2012070431/5000000000 : ℝ), (2312303789/5000000000 : ℝ)] ![(8311671361979/25000000000000 : ℝ), (30344246916237/100000000000000 : ℝ), (36409067625597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314738469/10000000000 : ℝ)|^2163 ≤ (8311671361979/25000000000000 : ℝ)^1651
        have hw : |(4314738469/10000000000 : ℝ)|=(4314738469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012070431/5000000000 : ℝ)|^2163 ≤ (30344246916237/100000000000000 : ℝ)^1651
        have hw : |(2012070431/5000000000 : ℝ)|=(2012070431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312303789/5000000000 : ℝ)|^2163 ≤ (36409067625597/100000000000000 : ℝ)^1651
        have hw : |(2312303789/5000000000 : ℝ)|=(2312303789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007284613/5000000000 : ℝ)*x 0 + (5190982887/10000000000 : ℝ)*x 1 + (5471606017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007284613/5000000000 : ℝ)^2163 ≤ (6128703405957/50000000000000 : ℝ)^1651 := by
    have hnat : (1007284613 : ℕ)^2163*50000000000000^1651 ≤ 6128703405957^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007284613 5000000000 6128703405957 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190982887/10000000000 : ℝ)^2163 ≤ (42358854072113/100000000000000 : ℝ)^1651 := by
    have hnat : (5190982887 : ℕ)^2163*100000000000000^1651 ≤ 42358854072113^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190982887 10000000000 42358854072113 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471606017/10000000000 : ℝ)^2163 ≤ (22691869553419/50000000000000 : ℝ)^1651 := by
    have hnat : (5471606017 : ℕ)^2163*50000000000000^1651 ≤ 22691869553419^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471606017 10000000000 22691869553419 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007284613/5000000000 : ℝ), (5190982887/10000000000 : ℝ), (5471606017/10000000000 : ℝ)] ![(6128703405957/50000000000000 : ℝ), (42358854072113/100000000000000 : ℝ), (22691869553419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007284613/5000000000 : ℝ)|^2163 ≤ (6128703405957/50000000000000 : ℝ)^1651
        have hw : |(-1007284613/5000000000 : ℝ)|=(1007284613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190982887/10000000000 : ℝ)|^2163 ≤ (42358854072113/100000000000000 : ℝ)^1651
        have hw : |(5190982887/10000000000 : ℝ)|=(5190982887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471606017/10000000000 : ℝ)|^2163 ≤ (22691869553419/50000000000000 : ℝ)^1651
        have hw : |(5471606017/10000000000 : ℝ)|=(5471606017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290870379/10000000000 : ℝ)*x 0 + (-1878764813/10000000000 : ℝ)*x 1 + (5471605959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290870379/10000000000 : ℝ)^2163 ≤ (2714368020663/6250000000000 : ℝ)^1651 := by
    have hnat : (5290870379 : ℕ)^2163*6250000000000^1651 ≤ 2714368020663^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290870379 10000000000 2714368020663 6250000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878764813/10000000000 : ℝ)^2163 ≤ (11186373175901/100000000000000 : ℝ)^1651 := by
    have hnat : (1878764813 : ℕ)^2163*100000000000000^1651 ≤ 11186373175901^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878764813 10000000000 11186373175901 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471605959/10000000000 : ℝ)^2163 ≤ (45383738476573/100000000000000 : ℝ)^1651 := by
    have hnat : (5471605959 : ℕ)^2163*100000000000000^1651 ≤ 45383738476573^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471605959 10000000000 45383738476573 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290870379/10000000000 : ℝ), (-1878764813/10000000000 : ℝ), (5471605959/10000000000 : ℝ)] ![(2714368020663/6250000000000 : ℝ), (11186373175901/100000000000000 : ℝ), (45383738476573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290870379/10000000000 : ℝ)|^2163 ≤ (2714368020663/6250000000000 : ℝ)^1651
        have hw : |(5290870379/10000000000 : ℝ)|=(5290870379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878764813/10000000000 : ℝ)|^2163 ≤ (11186373175901/100000000000000 : ℝ)^1651
        have hw : |(-1878764813/10000000000 : ℝ)|=(1878764813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471605959/10000000000 : ℝ)|^2163 ≤ (45383738476573/100000000000000 : ℝ)^1651
        have hw : |(5471605959/10000000000 : ℝ)|=(5471605959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (82669849/156250000 : ℝ)*x 0 + (5471606019/10000000000 : ℝ)*x 1 + (-1878764789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82669849/156250000 : ℝ)^2163 ≤ (8685977573637/20000000000000 : ℝ)^1651 := by
    have hnat : (82669849 : ℕ)^2163*20000000000000^1651 ≤ 8685977573637^1651*156250000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82669849 156250000 8685977573637 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471606019/10000000000 : ℝ)^2163 ≤ (45383739128571/100000000000000 : ℝ)^1651 := by
    have hnat : (5471606019 : ℕ)^2163*100000000000000^1651 ≤ 45383739128571^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471606019 10000000000 45383739128571 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878764789/10000000000 : ℝ)^2163 ≤ (11186372988687/100000000000000 : ℝ)^1651 := by
    have hnat : (1878764789 : ℕ)^2163*100000000000000^1651 ≤ 11186372988687^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878764789 10000000000 11186372988687 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82669849/156250000 : ℝ), (5471606019/10000000000 : ℝ), (-1878764789/10000000000 : ℝ)] ![(8685977573637/20000000000000 : ℝ), (45383739128571/100000000000000 : ℝ), (11186372988687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82669849/156250000 : ℝ)|^2163 ≤ (8685977573637/20000000000000 : ℝ)^1651
        have hw : |(82669849/156250000 : ℝ)|=(82669849/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471606019/10000000000 : ℝ)|^2163 ≤ (45383739128571/100000000000000 : ℝ)^1651
        have hw : |(5471606019/10000000000 : ℝ)|=(5471606019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1878764789/10000000000 : ℝ)|^2163 ≤ (11186372988687/100000000000000 : ℝ)^1651
        have hw : |(-1878764789/10000000000 : ℝ)|=(1878764789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s2_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269679011/625000000 : ℝ)*x 0 + (924187841/2000000000 : ℝ)*x 1 + (4027841461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269679011/625000000 : ℝ)^2163 ≤ (664959089141/2000000000000 : ℝ)^1651 := by
    have hnat : (269679011 : ℕ)^2163*2000000000000^1651 ≤ 664959089141^1651*625000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269679011 625000000 664959089141 2000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924187841/2000000000 : ℝ)^2163 ≤ (18185617600467/50000000000000 : ℝ)^1651 := by
    have hnat : (924187841 : ℕ)^2163*50000000000000^1651 ≤ 18185617600467^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924187841 2000000000 18185617600467 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027841461/10000000000 : ℝ)^2163 ≤ (30380810316051/100000000000000 : ℝ)^1651 := by
    have hnat : (4027841461 : ℕ)^2163*100000000000000^1651 ≤ 30380810316051^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027841461 10000000000 30380810316051 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269679011/625000000 : ℝ), (924187841/2000000000 : ℝ), (4027841461/10000000000 : ℝ)] ![(664959089141/2000000000000 : ℝ), (18185617600467/50000000000000 : ℝ), (30380810316051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269679011/625000000 : ℝ)|^2163 ≤ (664959089141/2000000000000 : ℝ)^1651
        have hw : |(269679011/625000000 : ℝ)|=(269679011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924187841/2000000000 : ℝ)|^2163 ≤ (18185617600467/50000000000000 : ℝ)^1651
        have hw : |(924187841/2000000000 : ℝ)|=(924187841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027841461/10000000000 : ℝ)|^2163 ≤ (30380810316051/100000000000000 : ℝ)^1651
        have hw : |(4027841461/10000000000 : ℝ)|=(4027841461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4821/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2001/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4003/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4821/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4821/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4821/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4821/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4821/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4821/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (7109/100000 : ℝ) ^ (4325/1024 : ℝ) ≤ (1414036974628843/100000000000000000000 : ℝ) := by
    have hpowers : (7109/100000 : ℝ)^4325 ≤ (1414036974628843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7109 : ℕ)^4325*100000000000000000000^1024 ≤ 1414036974628843^1024*100000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7109 100000 1414036974628843 100000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7109/100000 : ℝ)) (X := (1414036974628843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4821/25000 : ℝ) ^ (4325/1024 : ℝ) ≤ (23926276765971871/25000000000000000000 : ℝ) := by
    have hpowers : (4821/25000 : ℝ)^4325 ≤ (23926276765971871/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4821 : ℕ)^4325*25000000000000000000^1024 ≤ 23926276765971871^1024*25000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4821 25000 23926276765971871 25000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4821/25000 : ℝ)) (X := (23926276765971871/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001414036974628843/50000000000000000000 : ℝ) ≤ (10000066957606247/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50001414036974628843/50000000000000000000 : ℝ)^1024 ≤ (10000066957606247/10000000000000000 : ℝ)^4325 := by
      have hnat : (50001414036974628843 : ℕ)^1024*10000000000000000^4325 ≤ 10000066957606247^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001414036974628843 50000000000000000000 10000066957606247 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000066957606247/10000000000000000 : ℝ)) (X := (50001414036974628843/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100097119144038516327/100000000000000000000 : ℝ) ≤ (2000459714061971/2000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (100097119144038516327/100000000000000000000 : ℝ)^1024 ≤ (2000459714061971/2000000000000000 : ℝ)^4325 := by
      have hnat : (100097119144038516327 : ℕ)^1024*2000000000000000^4325 ≤ 2000459714061971^4325*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100097119144038516327 100000000000000000000 2000459714061971 2000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000459714061971/2000000000000000 : ℝ)) (X := (100097119144038516327/100000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12523926276765971871/12500000000000000000 : ℝ) ≤ (10004530183013463/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (12523926276765971871/12500000000000000000 : ℝ)^1024 ≤ (10004530183013463/10000000000000000 : ℝ)^4325 := by
      have hnat : (12523926276765971871 : ℕ)^1024*10000000000000000^4325 ≤ 10004530183013463^4325*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12523926276765971871 12500000000000000000 10004530183013463 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004530183013463/10000000000000000 : ℝ)) (X := (12523926276765971871/12500000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1414036974628843/100000000000000000000 : ℝ) ≤ ((121719086139436158681/121750000000000000000 : ℝ)+2*(278951587951/152187500000000 : ℝ)*(7109/100000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (121719086139436158681/121750000000000000000 : ℝ)+2*(278951587951/152187500000000 : ℝ)*(7109/100000 : ℝ)=(10000066957606247/10000000000000000 : ℝ) by norm_num, show 1+2*(1414036974628843/100000000000000000000 : ℝ)=(50001414036974628843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23926276765971871/25000000000000000000 : ℝ)+(1414036974628843/100000000000000000000 : ℝ) ≤ ((121719086139436158681/121750000000000000000 : ℝ)+(278951587951/152187500000000 : ℝ)*((4821/25000 : ℝ)+(7109/100000 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (121719086139436158681/121750000000000000000 : ℝ)+(278951587951/152187500000000 : ℝ)*((4821/25000 : ℝ)+(7109/100000 : ℝ))=(2000459714061971/2000000000000000 : ℝ) by norm_num, show 1+(23926276765971871/25000000000000000000 : ℝ)+(1414036974628843/100000000000000000000 : ℝ)=(100097119144038516327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23926276765971871/25000000000000000000 : ℝ) ≤ ((121719086139436158681/121750000000000000000 : ℝ)+2*(278951587951/152187500000000 : ℝ)*(4821/25000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (121719086139436158681/121750000000000000000 : ℝ)+2*(278951587951/152187500000000 : ℝ)*(4821/25000 : ℝ)=(10004530183013463/10000000000000000 : ℝ) by norm_num, show 1+2*(23926276765971871/25000000000000000000 : ℝ)=(12523926276765971871/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (121719086139436158681/121750000000000000000 : ℝ)*(X 1 0+X 2 0)+(278951587951/152187500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (7109/100000 : ℝ)) (hi := (4821/25000 : ℝ)) (c := (121719086139436158681/121750000000000000000 : ℝ)) (alpha := (278951587951/152187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (121719086139436158681/121750000000000000000 : ℝ)*(X 0 1+X 2 1)+(278951587951/152187500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (7109/100000 : ℝ)) (hi := (4821/25000 : ℝ)) (c := (121719086139436158681/121750000000000000000 : ℝ)) (alpha := (278951587951/152187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (121719086139436158681/121750000000000000000 : ℝ)*(X 0 2+X 1 2)+(278951587951/152187500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (7109/100000 : ℝ)) (hi := (4821/25000 : ℝ)) (c := (121719086139436158681/121750000000000000000 : ℝ)) (alpha := (278951587951/152187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100725493/500000000 : ℝ)*X 0 0+(5473357193/10000000000 : ℝ)*X 0 1+(518924697/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682143581/5000000000 : ℝ)*X 1 0+(-2161123851/10000000000 : ℝ)*X 1 1+(324327953/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2682143593/5000000000 : ℝ)*X 2 0+(518924721/1000000000 : ℝ)*X 2 1+(-216112387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314738469/10000000000 : ℝ)*X 0 0+(2012070431/5000000000 : ℝ)*X 0 1+(2312303789/5000000000 : ℝ)*X 0 2+(4314738469/10000000000 : ℝ)*X 1 0+(2012070431/5000000000 : ℝ)*X 1 1+(2312303789/5000000000 : ℝ)*X 1 2+(4314738469/10000000000 : ℝ)*X 2 0+(2012070431/5000000000 : ℝ)*X 2 1+(2312303789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1007284613/5000000000 : ℝ)*X 0 0+(5190982887/10000000000 : ℝ)*X 0 1+(5471606017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290870379/10000000000 : ℝ)*X 1 0+(-1878764813/10000000000 : ℝ)*X 1 1+(5471605959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82669849/156250000 : ℝ)*X 2 0+(5471606019/10000000000 : ℝ)*X 2 1+(-1878764789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269679011/625000000 : ℝ)*X 0 0+(924187841/2000000000 : ℝ)*X 0 1+(4027841461/10000000000 : ℝ)*X 0 2+(269679011/625000000 : ℝ)*X 1 0+(924187841/2000000000 : ℝ)*X 1 1+(4027841461/10000000000 : ℝ)*X 1 2+(269679011/625000000 : ℝ)*X 2 0+(924187841/2000000000 : ℝ)*X 2 1+(4027841461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212347785745522695828933/60875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467529047/100000000000000 : ℝ)*(base19) + (479977373/100000000000000 : ℝ)*(base23) + (1769827/100000000000000 : ℝ)*(lower2) + (17528117/25000000000000 : ℝ)*(upper3) + (56164677/100000000000000 : ℝ)*(upper5) + (1296289187952443/50000000000000 : ℝ)*(major0) + (1296289187952443/50000000000000 : ℝ)*(major1) + (1296289187952443/50000000000000 : ℝ)*(major2) + (3519769778293657/100000000000000 : ℝ)*(sp0) + (3519778258735237/100000000000000 : ℝ)*(sp1) + (351977824628691/10000000000000 : ℝ)*(sp2) + (1665374471179441/100000000000000 : ℝ)*(sp3) + (8947970627/100000000000000 : ℝ)*(sp4) + (3438090729/100000000000000 : ℝ)*(sp7) + (166537790927017/10000000000000 : ℝ)*(f.failure) + (879944681566071/25000000000000 : ℝ)*(f.sum) + (155559159634063/60875000000000000000000000000 : ℝ)*base65 + (56626934920576507683/6087500000000000000000000000000000 : ℝ)*base67 + (27039162124085992317/6087500000000000000000000000000000 : ℝ)*base70 + (26377940506451507683/6087500000000000000000000000000000 : ℝ)*base71 + (37453847747797/15218750000000000000000000000 : ℝ)*base73 + (6176969845948492317/6087500000000000000000000000000000 : ℝ)*base76 + (17430192377823492317/6087500000000000000000000000000000 : ℝ)*base78 + (58854131107451507683/6087500000000000000000000000000000 : ℝ)*base79 + (134470850900063/60875000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5290657/1000000000000000000000 : ℝ)*base90 + (5290657/1000000000000000000000 : ℝ)*base92 + (5290657/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4549474366294372801617672171/760937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (643285681/50000000000000 : ℝ)*(base19) + (1400996639/100000000000000 : ℝ)*(base23) + (4397319/3125000000000 : ℝ)*(upper3) + (58172939/100000000000000 : ℝ)*(lower4) + (94916909/100000000000000 : ℝ)*(upper5) + (656194922047097/25000000000000 : ℝ)*(major0) + (656194922047097/25000000000000 : ℝ)*(major1) + (656194922047097/25000000000000 : ℝ)*(major2) + (3729544243/25000000000000 : ℝ)*(sp1) + (1732783099/10000000000000 : ℝ)*(sp2) + (3563496317794887/100000000000000 : ℝ)*(sp4) + (1781740056523277/50000000000000 : ℝ)*(sp5) + (1781738794483629/50000000000000 : ℝ)*(sp6) + (421515714822343/25000000000000 : ℝ)*(sp7) + (421515714822343/25000000000000 : ℝ)*(f.failure) + (3563496317794887/100000000000000 : ℝ)*(f.sum) + (97377584722577/30437500000000000000000000000 : ℝ)*base65 + (4677168036976249057/3043750000000000000000000000000000 : ℝ)*base67 + (6396784443986250943/3043750000000000000000000000000000 : ℝ)*base70 + (9354723007717500943/3043750000000000000000000000000000 : ℝ)*base72 + (174373025084327/30437500000000000000000000000 : ℝ)*base73 + (30009445938242500943/3043750000000000000000000000000000 : ℝ)*base76 + (14553129625380000943/3043750000000000000000000000000000 : ℝ)*base78 + (10793193657217500943/3043750000000000000000000000000000 : ℝ)*base80 + (97704708101327/30437500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (17490097/2500000000000000000000 : ℝ)*base89 + (17490097/2500000000000000000000 : ℝ)*base91 + (17490097/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1366_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4821/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1366_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1366_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1366_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1366_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1366_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
