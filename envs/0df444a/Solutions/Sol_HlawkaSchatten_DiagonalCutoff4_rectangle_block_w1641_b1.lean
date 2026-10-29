-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1641_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:15.761996+00:00
-- url     : https://prove2.me/submissions/8850c805-0687-4138-b0b0-5bc0695b9ddd

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
theorem support_rectangle_w1641_s3_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1629211499/10000000000 : ℝ)*x 0 + (1362578663/2500000000 : ℝ)*x 1 + (2591599291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1629211499/10000000000 : ℝ)^4883 ≤ (5033183468319/50000000000000 : ℝ)^3859 := by
    have hnat : (1629211499 : ℕ)^4883*50000000000000^3859 ≤ 5033183468319^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629211499 10000000000 5033183468319 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362578663/2500000000 : ℝ)^4883 ≤ (46395948757433/100000000000000 : ℝ)^3859 := by
    have hnat : (1362578663 : ℕ)^4883*100000000000000^3859 ≤ 46395948757433^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362578663 2500000000 46395948757433 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591599291/5000000000 : ℝ)^4883 ≤ (43537684294523/100000000000000 : ℝ)^3859 := by
    have hnat : (2591599291 : ℕ)^4883*100000000000000^3859 ≤ 43537684294523^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591599291 5000000000 43537684294523 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1629211499/10000000000 : ℝ), (1362578663/2500000000 : ℝ), (2591599291/5000000000 : ℝ)] ![(5033183468319/50000000000000 : ℝ), (46395948757433/100000000000000 : ℝ), (43537684294523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1629211499/10000000000 : ℝ)|^4883 ≤ (5033183468319/50000000000000 : ℝ)^3859
        have hw : |(-1629211499/10000000000 : ℝ)|=(1629211499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362578663/2500000000 : ℝ)|^4883 ≤ (46395948757433/100000000000000 : ℝ)^3859
        have hw : |(1362578663/2500000000 : ℝ)|=(1362578663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591599291/5000000000 : ℝ)|^4883 ≤ (43537684294523/100000000000000 : ℝ)^3859
        have hw : |(2591599291/5000000000 : ℝ)|=(2591599291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674560553/5000000000 : ℝ)*x 0 + (-1766773321/10000000000 : ℝ)*x 1 + (2591599279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674560553/5000000000 : ℝ)^4883 ≤ (9061730852317/20000000000000 : ℝ)^3859 := by
    have hnat : (2674560553 : ℕ)^4883*20000000000000^3859 ≤ 9061730852317^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674560553 5000000000 9061730852317 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1766773321/10000000000 : ℝ)^4883 ≤ (5576830840891/50000000000000 : ℝ)^3859 := by
    have hnat : (1766773321 : ℕ)^4883*50000000000000^3859 ≤ 5576830840891^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766773321 10000000000 5576830840891 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591599279/5000000000 : ℝ)^4883 ≤ (8707536807887/20000000000000 : ℝ)^3859 := by
    have hnat : (2591599279 : ℕ)^4883*20000000000000^3859 ≤ 8707536807887^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591599279 5000000000 8707536807887 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674560553/5000000000 : ℝ), (-1766773321/10000000000 : ℝ), (2591599279/5000000000 : ℝ)] ![(9061730852317/20000000000000 : ℝ), (5576830840891/50000000000000 : ℝ), (8707536807887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674560553/5000000000 : ℝ)|^4883 ≤ (9061730852317/20000000000000 : ℝ)^3859
        have hw : |(2674560553/5000000000 : ℝ)|=(2674560553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1766773321/10000000000 : ℝ)|^4883 ≤ (5576830840891/50000000000000 : ℝ)^3859
        have hw : |(-1766773321/10000000000 : ℝ)|=(1766773321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591599279/5000000000 : ℝ)|^4883 ≤ (8707536807887/20000000000000 : ℝ)^3859
        have hw : |(2591599279/5000000000 : ℝ)|=(2591599279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213964849/400000000 : ℝ)*x 0 + (5183198491/10000000000 : ℝ)*x 1 + (-1766773251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213964849/400000000 : ℝ)^4883 ≤ (22654327768509/50000000000000 : ℝ)^3859 := by
    have hnat : (213964849 : ℕ)^4883*50000000000000^3859 ≤ 22654327768509^3859*400000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213964849 400000000 22654327768509 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183198491/10000000000 : ℝ)^4883 ≤ (43537683327313/100000000000000 : ℝ)^3859 := by
    have hnat : (5183198491 : ℕ)^4883*100000000000000^3859 ≤ 43537683327313^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183198491 10000000000 43537683327313 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1766773251/10000000000 : ℝ)^4883 ≤ (11153661122609/100000000000000 : ℝ)^3859 := by
    have hnat : (1766773251 : ℕ)^4883*100000000000000^3859 ≤ 11153661122609^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766773251 10000000000 11153661122609 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213964849/400000000 : ℝ), (5183198491/10000000000 : ℝ), (-1766773251/10000000000 : ℝ)] ![(22654327768509/50000000000000 : ℝ), (43537683327313/100000000000000 : ℝ), (11153661122609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213964849/400000000 : ℝ)|^4883 ≤ (22654327768509/50000000000000 : ℝ)^3859
        have hw : |(213964849/400000000 : ℝ)|=(213964849/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183198491/10000000000 : ℝ)|^4883 ≤ (43537683327313/100000000000000 : ℝ)^3859
        have hw : |(5183198491/10000000000 : ℝ)|=(5183198491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1766773251/10000000000 : ℝ)|^4883 ≤ (11153661122609/100000000000000 : ℝ)^3859
        have hw : |(-1766773251/10000000000 : ℝ)|=(1766773251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4187667347/10000000000 : ℝ)*x 0 + (3856274743/10000000000 : ℝ)*x 1 + (4539541831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187667347/10000000000 : ℝ)^4883 ≤ (8310001369429/25000000000000 : ℝ)^3859 := by
    have hnat : (4187667347 : ℕ)^4883*25000000000000^3859 ≤ 8310001369429^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187667347 10000000000 8310001369429 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3856274743/10000000000 : ℝ)^4883 ≤ (374339893437/1250000000000 : ℝ)^3859 := by
    have hnat : (3856274743 : ℕ)^4883*1250000000000^3859 ≤ 374339893437^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856274743 10000000000 374339893437 1250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4539541831/10000000000 : ℝ)^4883 ≤ (36812803030111/100000000000000 : ℝ)^3859 := by
    have hnat : (4539541831 : ℕ)^4883*100000000000000^3859 ≤ 36812803030111^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539541831 10000000000 36812803030111 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187667347/10000000000 : ℝ), (3856274743/10000000000 : ℝ), (4539541831/10000000000 : ℝ)] ![(8310001369429/25000000000000 : ℝ), (374339893437/1250000000000 : ℝ), (36812803030111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187667347/10000000000 : ℝ)|^4883 ≤ (8310001369429/25000000000000 : ℝ)^3859
        have hw : |(4187667347/10000000000 : ℝ)|=(4187667347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3856274743/10000000000 : ℝ)|^4883 ≤ (374339893437/1250000000000 : ℝ)^3859
        have hw : |(3856274743/10000000000 : ℝ)|=(3856274743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4539541831/10000000000 : ℝ)|^4883 ≤ (36812803030111/100000000000000 : ℝ)^3859
        have hw : |(4539541831/10000000000 : ℝ)|=(4539541831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1629277241/10000000000 : ℝ)*x 0 + (5185213853/10000000000 : ℝ)*x 1 + (5448278153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1629277241/10000000000 : ℝ)^4883 ≤ (10066880924039/100000000000000 : ℝ)^3859 := by
    have hnat : (1629277241 : ℕ)^4883*100000000000000^3859 ≤ 10066880924039^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629277241 10000000000 10066880924039 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185213853/10000000000 : ℝ)^4883 ≤ (43559105074459/100000000000000 : ℝ)^3859 := by
    have hnat : (5185213853 : ℕ)^4883*100000000000000^3859 ≤ 43559105074459^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185213853 10000000000 43559105074459 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448278153/10000000000 : ℝ)^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859 := by
    have hnat : (5448278153 : ℕ)^4883*20000000000000^3859 ≤ 9274802797341^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448278153 10000000000 9274802797341 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1629277241/10000000000 : ℝ), (5185213853/10000000000 : ℝ), (5448278153/10000000000 : ℝ)] ![(10066880924039/100000000000000 : ℝ), (43559105074459/100000000000000 : ℝ), (9274802797341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1629277241/10000000000 : ℝ)|^4883 ≤ (10066880924039/100000000000000 : ℝ)^3859
        have hw : |(-1629277241/10000000000 : ℝ)|=(1629277241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185213853/10000000000 : ℝ)|^4883 ≤ (43559105074459/100000000000000 : ℝ)^3859
        have hw : |(5185213853/10000000000 : ℝ)|=(5185213853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448278153/10000000000 : ℝ)|^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859
        have hw : |(5448278153/10000000000 : ℝ)|=(5448278153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055567961/2000000000 : ℝ)*x 0 + (-12013549/80000000 : ℝ)*x 1 + (5448278153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055567961/2000000000 : ℝ)^4883 ≤ (44546021868403/100000000000000 : ℝ)^3859 := by
    have hnat : (1055567961 : ℕ)^4883*100000000000000^3859 ≤ 44546021868403^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055567961 2000000000 44546021868403 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12013549/80000000 : ℝ)^4883 ≤ (9079964131831/100000000000000 : ℝ)^3859 := by
    have hnat : (12013549 : ℕ)^4883*100000000000000^3859 ≤ 9079964131831^3859*80000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12013549 80000000 9079964131831 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448278153/10000000000 : ℝ)^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859 := by
    have hnat : (5448278153 : ℕ)^4883*20000000000000^3859 ≤ 9274802797341^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448278153 10000000000 9274802797341 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055567961/2000000000 : ℝ), (-12013549/80000000 : ℝ), (5448278153/10000000000 : ℝ)] ![(44546021868403/100000000000000 : ℝ), (9079964131831/100000000000000 : ℝ), (9274802797341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055567961/2000000000 : ℝ)|^4883 ≤ (44546021868403/100000000000000 : ℝ)^3859
        have hw : |(1055567961/2000000000 : ℝ)|=(1055567961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12013549/80000000 : ℝ)|^4883 ≤ (9079964131831/100000000000000 : ℝ)^3859
        have hw : |(-12013549/80000000 : ℝ)|=(12013549/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448278153/10000000000 : ℝ)|^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859
        have hw : |(5448278153/10000000000 : ℝ)|=(5448278153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319459951/2500000000 : ℝ)*x 0 + (5448278153/10000000000 : ℝ)*x 1 + (-1501693627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319459951/2500000000 : ℝ)^4883 ≤ (44546021857723/100000000000000 : ℝ)^3859 := by
    have hnat : (1319459951 : ℕ)^4883*100000000000000^3859 ≤ 44546021857723^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319459951 2500000000 44546021857723 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448278153/10000000000 : ℝ)^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859 := by
    have hnat : (5448278153 : ℕ)^4883*20000000000000^3859 ≤ 9274802797341^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448278153 10000000000 9274802797341 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501693627/10000000000 : ℝ)^4883 ≤ (9079964147133/100000000000000 : ℝ)^3859 := by
    have hnat : (1501693627 : ℕ)^4883*100000000000000^3859 ≤ 9079964147133^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501693627 10000000000 9079964147133 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319459951/2500000000 : ℝ), (5448278153/10000000000 : ℝ), (-1501693627/10000000000 : ℝ)] ![(44546021857723/100000000000000 : ℝ), (9274802797341/20000000000000 : ℝ), (9079964147133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319459951/2500000000 : ℝ)|^4883 ≤ (44546021857723/100000000000000 : ℝ)^3859
        have hw : |(1319459951/2500000000 : ℝ)|=(1319459951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448278153/10000000000 : ℝ)|^4883 ≤ (9274802797341/20000000000000 : ℝ)^3859
        have hw : |(5448278153/10000000000 : ℝ)|=(5448278153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1501693627/10000000000 : ℝ)|^4883 ≤ (9079964147133/100000000000000 : ℝ)^3859
        have hw : |(-1501693627/10000000000 : ℝ)|=(1501693627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s3_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093917713/5000000000 : ℝ)*x 0 + (1133596703/2500000000 : ℝ)*x 1 + (3861484259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093917713/5000000000 : ℝ)^4883 ≤ (33241693649453/100000000000000 : ℝ)^3859 := by
    have hnat : (2093917713 : ℕ)^4883*100000000000000^3859 ≤ 33241693649453^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093917713 5000000000 33241693649453 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133596703/2500000000 : ℝ)^4883 ≤ (36759914240939/100000000000000 : ℝ)^3859 := by
    have hnat : (1133596703 : ℕ)^4883*100000000000000^3859 ≤ 36759914240939^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133596703 2500000000 36759914240939 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3861484259/10000000000 : ℝ)^4883 ≤ (29998392099883/100000000000000 : ℝ)^3859 := by
    have hnat : (3861484259 : ℕ)^4883*100000000000000^3859 ≤ 29998392099883^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861484259 10000000000 29998392099883 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093917713/5000000000 : ℝ), (1133596703/2500000000 : ℝ), (3861484259/10000000000 : ℝ)] ![(33241693649453/100000000000000 : ℝ), (36759914240939/100000000000000 : ℝ), (29998392099883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093917713/5000000000 : ℝ)|^4883 ≤ (33241693649453/100000000000000 : ℝ)^3859
        have hw : |(2093917713/5000000000 : ℝ)|=(2093917713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133596703/2500000000 : ℝ)|^4883 ≤ (36759914240939/100000000000000 : ℝ)^3859
        have hw : |(1133596703/2500000000 : ℝ)|=(1133596703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3861484259/10000000000 : ℝ)|^4883 ≤ (29998392099883/100000000000000 : ℝ)^3859
        have hw : |(3861484259/10000000000 : ℝ)|=(3861484259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10617/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16291/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2047/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2047/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2047/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2047/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2047/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2047/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10541/100000 : ℝ) ^ (4879/1024 : ℝ) ≤ (1104956962931723/50000000000000000000 : ℝ) := by
    have hpowers : (10541/100000 : ℝ)^4879 ≤ (1104956962931723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10541 : ℕ)^4879*50000000000000000000^1024 ≤ 1104956962931723^1024*100000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10541 100000 1104956962931723 50000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10541/100000 : ℝ)) (X := (1104956962931723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2047/12500 : ℝ) ^ (4879/1024 : ℝ) ≤ (14085315967989/78125000000000000 : ℝ) := by
    have hpowers : (2047/12500 : ℝ)^4879 ≤ (14085315967989/78125000000000000 : ℝ)^1024 := by
      have hnat : (2047 : ℕ)^4879*78125000000000000^1024 ≤ 14085315967989^1024*12500^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2047 12500 14085315967989 78125000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2047/12500 : ℝ)) (X := (14085315967989/78125000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001104956962931723/25000000000000000000 : ℝ) ≤ (10000092761317801/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (25001104956962931723/25000000000000000000 : ℝ)^1024 ≤ (10000092761317801/10000000000000000 : ℝ)^4879 := by
      have hnat : (25001104956962931723 : ℕ)^1024*10000000000000000^4879 ≤ 10000092761317801^4879*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001104956962931723 25000000000000000000 10000092761317801 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000092761317801/10000000000000000 : ℝ)) (X := (25001104956962931723/25000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010119559182444683/50000000000000000000 : ℝ) ≤ (10000424742781583/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (50010119559182444683/50000000000000000000 : ℝ)^1024 ≤ (10000424742781583/10000000000000000 : ℝ)^4879 := by
      have hnat : (50010119559182444683 : ℕ)^1024*10000000000000000^4879 ≤ 10000424742781583^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010119559182444683 50000000000000000000 10000424742781583 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424742781583/10000000000000000 : ℝ)) (X := (50010119559182444683/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (39076585315967989/39062500000000000 : ℝ) ≤ (2000151344849073/2000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (39076585315967989/39062500000000000 : ℝ)^1024 ≤ (2000151344849073/2000000000000000 : ℝ)^4879 := by
      have hnat : (39076585315967989 : ℕ)^1024*2000000000000000^4879 ≤ 2000151344849073^4879*39062500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39076585315967989 39062500000000000 2000151344849073 2000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000151344849073/2000000000000000 : ℝ)) (X := (39076585315967989/39062500000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1104956962931723/50000000000000000000 : ℝ) ≤ ((58343542429069916711/58350000000000000000 : ℝ)+2*(165990731891/291750000000000 : ℝ)*(10541/100000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (58343542429069916711/58350000000000000000 : ℝ)+2*(165990731891/291750000000000 : ℝ)*(10541/100000 : ℝ)=(10000092761317801/10000000000000000 : ℝ) by norm_num, show 1+2*(1104956962931723/50000000000000000000 : ℝ)=(25001104956962931723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14085315967989/78125000000000000 : ℝ)+(1104956962931723/50000000000000000000 : ℝ) ≤ ((58343542429069916711/58350000000000000000 : ℝ)+(165990731891/291750000000000 : ℝ)*((2047/12500 : ℝ)+(10541/100000 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (58343542429069916711/58350000000000000000 : ℝ)+(165990731891/291750000000000 : ℝ)*((2047/12500 : ℝ)+(10541/100000 : ℝ))=(10000424742781583/10000000000000000 : ℝ) by norm_num, show 1+(14085315967989/78125000000000000 : ℝ)+(1104956962931723/50000000000000000000 : ℝ)=(50010119559182444683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14085315967989/78125000000000000 : ℝ) ≤ ((58343542429069916711/58350000000000000000 : ℝ)+2*(165990731891/291750000000000 : ℝ)*(2047/12500 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (58343542429069916711/58350000000000000000 : ℝ)+2*(165990731891/291750000000000 : ℝ)*(2047/12500 : ℝ)=(2000151344849073/2000000000000000 : ℝ) by norm_num, show 1+2*(14085315967989/78125000000000000 : ℝ)=(39076585315967989/39062500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58343542429069916711/58350000000000000000 : ℝ)*(X 1 0+X 2 0)+(165990731891/291750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (58343542429069916711/58350000000000000000 : ℝ)) (alpha := (165990731891/291750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58343542429069916711/58350000000000000000 : ℝ)*(X 0 1+X 2 1)+(165990731891/291750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (58343542429069916711/58350000000000000000 : ℝ)) (alpha := (165990731891/291750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58343542429069916711/58350000000000000000 : ℝ)*(X 0 2+X 1 2)+(165990731891/291750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (2047/12500 : ℝ)) (c := (58343542429069916711/58350000000000000000 : ℝ)) (alpha := (165990731891/291750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1629211499/10000000000 : ℝ)*X 0 0+(1362578663/2500000000 : ℝ)*X 0 1+(2591599291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674560553/5000000000 : ℝ)*X 1 0+(-1766773321/10000000000 : ℝ)*X 1 1+(2591599279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213964849/400000000 : ℝ)*X 2 0+(5183198491/10000000000 : ℝ)*X 2 1+(-1766773251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4187667347/10000000000 : ℝ)*X 0 0+(3856274743/10000000000 : ℝ)*X 0 1+(4539541831/10000000000 : ℝ)*X 0 2+(4187667347/10000000000 : ℝ)*X 1 0+(3856274743/10000000000 : ℝ)*X 1 1+(4539541831/10000000000 : ℝ)*X 1 2+(4187667347/10000000000 : ℝ)*X 2 0+(3856274743/10000000000 : ℝ)*X 2 1+(4539541831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1629277241/10000000000 : ℝ)*X 0 0+(5185213853/10000000000 : ℝ)*X 0 1+(5448278153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055567961/2000000000 : ℝ)*X 1 0+(-12013549/80000000 : ℝ)*X 1 1+(5448278153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319459951/2500000000 : ℝ)*X 2 0+(5448278153/10000000000 : ℝ)*X 2 1+(-1501693627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093917713/5000000000 : ℝ)*X 0 0+(1133596703/2500000000 : ℝ)*X 0 1+(3861484259/10000000000 : ℝ)*X 0 2+(2093917713/5000000000 : ℝ)*X 1 0+(1133596703/2500000000 : ℝ)*X 1 1+(3861484259/10000000000 : ℝ)*X 1 2+(2093917713/5000000000 : ℝ)*X 2 0+(1133596703/2500000000 : ℝ)*X 2 1+(3861484259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113156509742162158557514279/24312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (736884797/100000000000000 : ℝ)*(base19) + (374377829/50000000000000 : ℝ)*(base23) + (9550061/25000000000000 : ℝ)*(lower2) + (106028019/100000000000000 : ℝ)*(upper3) + (15191503/12500000000000 : ℝ)*(upper5) + (130181788682089/5000000000000 : ℝ)*(major0) + (130181788682089/5000000000000 : ℝ)*(major1) + (130181788682089/5000000000000 : ℝ)*(major2) + (233981156667457/6250000000000 : ℝ)*(sp0) + (1871853410516813/50000000000000 : ℝ)*(sp1) + (1871853404581383/50000000000000 : ℝ)*(sp2) + (731780026822929/50000000000000 : ℝ)*(sp3) + (1131404889/12500000000000 : ℝ)*(sp4) + (472572191/12500000000000 : ℝ)*(sp7) + (731781917111693/50000000000000 : ℝ)*(f.failure) + (467963444739803/12500000000000 : ℝ)*(f.sum) + (4823427654551/2917500000000000000000000000 : ℝ)*base65 + (439172575311736907/97250000000000000000000000000000 : ℝ)*base68 + (1172831465041736907/97250000000000000000000000000000 : ℝ)*base70 + (121260422943263093/97250000000000000000000000000000 : ℝ)*base71 + (926434547563/1458750000000000000000000000 : ℝ)*base73 + (723230670974736907/97250000000000000000000000000000 : ℝ)*base76 + (123614881973236907/97250000000000000000000000000000 : ℝ)*base78 + (1342419697510236907/97250000000000000000000000000000 : ℝ)*base80 + (5141983249187/1458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2358491/2500000000000000000000 : ℝ)*base89 + (2358491/2500000000000000000000 : ℝ)*base91 + (2358491/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2231214852618674781019307997/486250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341575949/50000000000000 : ℝ)*(base19) + (184567643/25000000000000 : ℝ)*(base23) + (96168029/100000000000000 : ℝ)*(upper3) + (6349837/25000000000000 : ℝ)*(lower4) + (47872617/50000000000000 : ℝ)*(upper5) + (1321862730319609/50000000000000 : ℝ)*(major0) + (1321862730319609/50000000000000 : ℝ)*(major1) + (1321862730319609/50000000000000 : ℝ)*(major2) + (4051306021/50000000000000 : ℝ)*(sp1) + (8673790771/100000000000000 : ℝ)*(sp2) + (380135159463133/10000000000000 : ℝ)*(sp4) + (3801342808867389/100000000000000 : ℝ)*(sp5) + (1900671091284993/50000000000000 : ℝ)*(sp6) + (1486099173693207/100000000000000 : ℝ)*(sp7) + (1486099173693207/100000000000000 : ℝ)*(f.failure) + (380135159463133/10000000000000 : ℝ)*(f.sum) + (1679477683703/3646875000000000000000000000 : ℝ)*base66 + (12373128565493704667/972500000000000000000000000000000 : ℝ)*base68 + (9430597902446204667/972500000000000000000000000000000 : ℝ)*base70 + (8623682244856204667/972500000000000000000000000000000 : ℝ)*base72 + (60949316938999/29175000000000000000000000000 : ℝ)*base74 + (14256487617713704667/972500000000000000000000000000000 : ℝ)*base76 + (9857939977251204667/972500000000000000000000000000000 : ℝ)*base78 + (7384619726446204667/972500000000000000000000000000000 : ℝ)*base80 + (43463709714887/14587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (64827809/5000000000000000000000 : ℝ)*base89 + (64827809/5000000000000000000000 : ℝ)*base91 + (64827809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1641_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1641_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1641_s4_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12728659/78125000 : ℝ)*x 0 + (5450030247/10000000000 : ℝ)*x 1 + (2591722491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12728659/78125000 : ℝ)^4883 ≤ (10066811427291/100000000000000 : ℝ)^3859 := by
    have hnat : (12728659 : ℕ)^4883*100000000000000^3859 ≤ 10066811427291^3859*78125000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12728659 78125000 10066811427291 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450030247/10000000000 : ℝ)^4883 ≤ (46392885350781/100000000000000 : ℝ)^3859 := by
    have hnat : (5450030247 : ℕ)^4883*100000000000000^3859 ≤ 46392885350781^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450030247 10000000000 46392885350781 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591722491/5000000000 : ℝ)^4883 ≤ (8708060643669/20000000000000 : ℝ)^3859 := by
    have hnat : (2591722491 : ℕ)^4883*20000000000000^3859 ≤ 8708060643669^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591722491 5000000000 8708060643669 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12728659/78125000 : ℝ), (5450030247/10000000000 : ℝ), (2591722491/5000000000 : ℝ)] ![(10066811427291/100000000000000 : ℝ), (46392885350781/100000000000000 : ℝ), (8708060643669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12728659/78125000 : ℝ)|^4883 ≤ (10066811427291/100000000000000 : ℝ)^3859
        have hw : |(-12728659/78125000 : ℝ)|=(12728659/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450030247/10000000000 : ℝ)|^4883 ≤ (46392885350781/100000000000000 : ℝ)^3859
        have hw : |(5450030247/10000000000 : ℝ)|=(5450030247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591722491/5000000000 : ℝ)|^4883 ≤ (8708060643669/20000000000000 : ℝ)^3859
        have hw : |(2591722491/5000000000 : ℝ)|=(2591722491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674522121/5000000000 : ℝ)*x 0 + (-353309641/2000000000 : ℝ)*x 1 + (5183445253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674522121/5000000000 : ℝ)^4883 ≤ (9061566088127/20000000000000 : ℝ)^3859 := by
    have hnat : (2674522121 : ℕ)^4883*20000000000000^3859 ≤ 9061566088127^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674522121 5000000000 9061566088127 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353309641/2000000000 : ℝ)^4883 ≤ (5575931721/50000000000 : ℝ)^3859 := by
    have hnat : (353309641 : ℕ)^4883*50000000000^3859 ≤ 5575931721^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353309641 2000000000 5575931721 50000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183445253/10000000000 : ℝ)^4883 ≤ (21770153049377/50000000000000 : ℝ)^3859 := by
    have hnat : (5183445253 : ℕ)^4883*50000000000000^3859 ≤ 21770153049377^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183445253 10000000000 21770153049377 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674522121/5000000000 : ℝ), (-353309641/2000000000 : ℝ), (5183445253/10000000000 : ℝ)] ![(9061566088127/20000000000000 : ℝ), (5575931721/50000000000 : ℝ), (21770153049377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674522121/5000000000 : ℝ)|^4883 ≤ (9061566088127/20000000000000 : ℝ)^3859
        have hw : |(2674522121/5000000000 : ℝ)|=(2674522121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353309641/2000000000 : ℝ)|^4883 ≤ (5575931721/50000000000 : ℝ)^3859
        have hw : |(-353309641/2000000000 : ℝ)|=(353309641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183445253/10000000000 : ℝ)|^4883 ≤ (21770153049377/50000000000000 : ℝ)^3859
        have hw : |(5183445253/10000000000 : ℝ)|=(5183445253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133726107/250000000 : ℝ)*x 0 + (518344499/1000000000 : ℝ)*x 1 + (-353309701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133726107/250000000 : ℝ)^4883 ≤ (9061566169583/20000000000000 : ℝ)^3859 := by
    have hnat : (133726107 : ℕ)^4883*20000000000000^3859 ≤ 9061566169583^3859*250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133726107 250000000 9061566169583 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518344499/1000000000 : ℝ)^4883 ≤ (2721268956461/6250000000000 : ℝ)^3859 := by
    have hnat : (518344499 : ℕ)^4883*6250000000000^3859 ≤ 2721268956461^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518344499 1000000000 2721268956461 6250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353309701/2000000000 : ℝ)^4883 ≤ (11151865838377/100000000000000 : ℝ)^3859 := by
    have hnat : (353309701 : ℕ)^4883*100000000000000^3859 ≤ 11151865838377^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353309701 2000000000 11151865838377 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133726107/250000000 : ℝ), (518344499/1000000000 : ℝ), (-353309701/2000000000 : ℝ)] ![(9061566169583/20000000000000 : ℝ), (2721268956461/6250000000000 : ℝ), (11151865838377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133726107/250000000 : ℝ)|^4883 ≤ (9061566169583/20000000000000 : ℝ)^3859
        have hw : |(133726107/250000000 : ℝ)|=(133726107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518344499/1000000000 : ℝ)|^4883 ≤ (2721268956461/6250000000000 : ℝ)^3859
        have hw : |(518344499/1000000000 : ℝ)|=(518344499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353309701/2000000000 : ℝ)|^4883 ≤ (11151865838377/100000000000000 : ℝ)^3859
        have hw : |(-353309701/2000000000 : ℝ)|=(353309701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093851877/5000000000 : ℝ)*x 0 + (3856950349/10000000000 : ℝ)*x 1 + (4538859181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093851877/5000000000 : ℝ)^4883 ≤ (33240371145123/100000000000000 : ℝ)^3859 := by
    have hnat : (2093851877 : ℕ)^4883*100000000000000^3859 ≤ 33240371145123^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093851877 5000000000 33240371145123 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3856950349/10000000000 : ℝ)^4883 ≤ (14976915245129/50000000000000 : ℝ)^3859 := by
    have hnat : (3856950349 : ℕ)^4883*50000000000000^3859 ≤ 14976915245129^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856950349 10000000000 14976915245129 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4538859181/10000000000 : ℝ)^4883 ≤ (36805798351083/100000000000000 : ℝ)^3859 := by
    have hnat : (4538859181 : ℕ)^4883*100000000000000^3859 ≤ 36805798351083^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538859181 10000000000 36805798351083 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093851877/5000000000 : ℝ), (3856950349/10000000000 : ℝ), (4538859181/10000000000 : ℝ)] ![(33240371145123/100000000000000 : ℝ), (14976915245129/50000000000000 : ℝ), (36805798351083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093851877/5000000000 : ℝ)|^4883 ≤ (33240371145123/100000000000000 : ℝ)^3859
        have hw : |(2093851877/5000000000 : ℝ)|=(2093851877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3856950349/10000000000 : ℝ)|^4883 ≤ (14976915245129/50000000000000 : ℝ)^3859
        have hw : |(3856950349/10000000000 : ℝ)|=(3856950349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4538859181/10000000000 : ℝ)|^4883 ≤ (36805798351083/100000000000000 : ℝ)^3859
        have hw : |(4538859181/10000000000 : ℝ)|=(4538859181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-325866691/2000000000 : ℝ)*x 0 + (324090781/625000000 : ℝ)*x 1 + (5448001813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325866691/2000000000 : ℝ)^4883 ≤ (10067320423517/100000000000000 : ℝ)^3859 := by
    have hnat : (325866691 : ℕ)^4883*100000000000000^3859 ≤ 10067320423517^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325866691 2000000000 10067320423517 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324090781/625000000 : ℝ)^4883 ≤ (43561641812219/100000000000000 : ℝ)^3859 := by
    have hnat : (324090781 : ℕ)^4883*100000000000000^3859 ≤ 43561641812219^3859*625000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324090781 625000000 43561641812219 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448001813/10000000000 : ℝ)^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859 := by
    have hnat : (5448001813 : ℕ)^4883*12500000000000^3859 ≤ 5796379718129^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448001813 10000000000 5796379718129 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-325866691/2000000000 : ℝ), (324090781/625000000 : ℝ), (5448001813/10000000000 : ℝ)] ![(10067320423517/100000000000000 : ℝ), (43561641812219/100000000000000 : ℝ), (5796379718129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-325866691/2000000000 : ℝ)|^4883 ≤ (10067320423517/100000000000000 : ℝ)^3859
        have hw : |(-325866691/2000000000 : ℝ)|=(325866691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324090781/625000000 : ℝ)|^4883 ≤ (43561641812219/100000000000000 : ℝ)^3859
        have hw : |(324090781/625000000 : ℝ)|=(324090781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448001813/10000000000 : ℝ)|^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859
        have hw : |(5448001813/10000000000 : ℝ)|=(5448001813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527790489/1000000000 : ℝ)*x 0 + (-187748971/1250000000 : ℝ)*x 1 + (5448001813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527790489/1000000000 : ℝ)^4883 ≤ (111366792417/250000000000 : ℝ)^3859 := by
    have hnat : (527790489 : ℕ)^4883*250000000000^3859 ≤ 111366792417^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527790489 1000000000 111366792417 250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187748971/1250000000 : ℝ)^4883 ≤ (9082245265833/100000000000000 : ℝ)^3859 := by
    have hnat : (187748971 : ℕ)^4883*100000000000000^3859 ≤ 9082245265833^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187748971 1250000000 9082245265833 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448001813/10000000000 : ℝ)^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859 := by
    have hnat : (5448001813 : ℕ)^4883*12500000000000^3859 ≤ 5796379718129^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448001813 10000000000 5796379718129 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527790489/1000000000 : ℝ), (-187748971/1250000000 : ℝ), (5448001813/10000000000 : ℝ)] ![(111366792417/250000000000 : ℝ), (9082245265833/100000000000000 : ℝ), (5796379718129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527790489/1000000000 : ℝ)|^4883 ≤ (111366792417/250000000000 : ℝ)^3859
        have hw : |(527790489/1000000000 : ℝ)|=(527790489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187748971/1250000000 : ℝ)|^4883 ≤ (9082245265833/100000000000000 : ℝ)^3859
        have hw : |(-187748971/1250000000 : ℝ)|=(187748971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448001813/10000000000 : ℝ)|^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859
        have hw : |(5448001813/10000000000 : ℝ)|=(5448001813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527790489/1000000000 : ℝ)*x 0 + (5448001813/10000000000 : ℝ)*x 1 + (-187748971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527790489/1000000000 : ℝ)^4883 ≤ (111366792417/250000000000 : ℝ)^3859 := by
    have hnat : (527790489 : ℕ)^4883*250000000000^3859 ≤ 111366792417^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527790489 1000000000 111366792417 250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448001813/10000000000 : ℝ)^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859 := by
    have hnat : (5448001813 : ℕ)^4883*12500000000000^3859 ≤ 5796379718129^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448001813 10000000000 5796379718129 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187748971/1250000000 : ℝ)^4883 ≤ (9082245265833/100000000000000 : ℝ)^3859 := by
    have hnat : (187748971 : ℕ)^4883*100000000000000^3859 ≤ 9082245265833^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187748971 1250000000 9082245265833 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527790489/1000000000 : ℝ), (5448001813/10000000000 : ℝ), (-187748971/1250000000 : ℝ)] ![(111366792417/250000000000 : ℝ), (5796379718129/12500000000000 : ℝ), (9082245265833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527790489/1000000000 : ℝ)|^4883 ≤ (111366792417/250000000000 : ℝ)^3859
        have hw : |(527790489/1000000000 : ℝ)|=(527790489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448001813/10000000000 : ℝ)|^4883 ≤ (5796379718129/12500000000000 : ℝ)^3859
        have hw : |(5448001813/10000000000 : ℝ)|=(5448001813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187748971/1250000000 : ℝ)|^4883 ≤ (9082245265833/100000000000000 : ℝ)^3859
        have hw : |(-187748971/1250000000 : ℝ)|=(187748971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s4_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261741957/625000000 : ℝ)*x 0 + (4533724247/10000000000 : ℝ)*x 1 + (1931069491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261741957/625000000 : ℝ)^4883 ≤ (4155256760979/12500000000000 : ℝ)^3859 := by
    have hnat : (261741957 : ℕ)^4883*12500000000000^3859 ≤ 4155256760979^3859*625000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261741957 625000000 4155256760979 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533724247/10000000000 : ℝ)^4883 ≤ (735062353999/2000000000000 : ℝ)^3859 := by
    have hnat : (4533724247 : ℕ)^4883*2000000000000^3859 ≤ 735062353999^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533724247 10000000000 735062353999 2000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931069491/5000000000 : ℝ)^4883 ≤ (1875301762713/6250000000000 : ℝ)^3859 := by
    have hnat : (1931069491 : ℕ)^4883*6250000000000^3859 ≤ 1875301762713^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931069491 5000000000 1875301762713 6250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261741957/625000000 : ℝ), (4533724247/10000000000 : ℝ), (1931069491/5000000000 : ℝ)] ![(4155256760979/12500000000000 : ℝ), (735062353999/2000000000000 : ℝ), (1875301762713/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261741957/625000000 : ℝ)|^4883 ≤ (4155256760979/12500000000000 : ℝ)^3859
        have hw : |(261741957/625000000 : ℝ)|=(261741957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533724247/10000000000 : ℝ)|^4883 ≤ (735062353999/2000000000000 : ℝ)^3859
        have hw : |(4533724247/10000000000 : ℝ)|=(4533724247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1931069491/5000000000 : ℝ)|^4883 ≤ (1875301762713/6250000000000 : ℝ)^3859
        have hw : |(1931069491/5000000000 : ℝ)|=(1931069491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5311/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3257/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10617/100000 : ℝ) ^ (4879/1024 : ℝ) ≤ (2286867912937713/100000000000000000000 : ℝ) := by
    have hpowers : (10617/100000 : ℝ)^4879 ≤ (2286867912937713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10617 : ℕ)^4879*100000000000000000000^1024 ≤ 2286867912937713^1024*100000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10617 100000 2286867912937713 100000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10617/100000 : ℝ)) (X := (2286867912937713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16291/100000 : ℝ) ^ (4879/1024 : ℝ) ≤ (1758765946913651/10000000000000000000 : ℝ) := by
    have hpowers : (16291/100000 : ℝ)^4879 ≤ (1758765946913651/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16291 : ℕ)^4879*10000000000000000000^1024 ≤ 1758765946913651^1024*100000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16291 100000 1758765946913651 10000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16291/100000 : ℝ)) (X := (1758765946913651/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002286867912937713/50000000000000000000 : ℝ) ≤ (10000095991409339/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (50002286867912937713/50000000000000000000 : ℝ)^1024 ≤ (10000095991409339/10000000000000000 : ℝ)^4879 := by
      have hnat : (50002286867912937713 : ℕ)^1024*10000000000000000^4879 ≤ 10000095991409339^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002286867912937713 50000000000000000000 10000095991409339 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000095991409339/10000000000000000 : ℝ)) (X := (50002286867912937713/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019874527382074223/100000000000000000000 : ℝ) ≤ (10000417091992231/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (100019874527382074223/100000000000000000000 : ℝ)^1024 ≤ (10000417091992231/10000000000000000 : ℝ)^4879 := by
      have hnat : (100019874527382074223 : ℕ)^1024*10000000000000000^4879 ≤ 10000417091992231^4879*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019874527382074223 100000000000000000000 10000417091992231 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417091992231/10000000000000000 : ℝ)) (X := (100019874527382074223/100000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001758765946913651/5000000000000000000 : ℝ) ≤ (10000738192575123/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (5001758765946913651/5000000000000000000 : ℝ)^1024 ≤ (10000738192575123/10000000000000000 : ℝ)^4879 := by
      have hnat : (5001758765946913651 : ℕ)^1024*10000000000000000^4879 ≤ 10000738192575123^4879*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001758765946913651 5000000000000000000 10000738192575123 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000738192575123/10000000000000000 : ℝ)) (X := (5001758765946913651/5000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2286867912937713/100000000000000000000 : ℝ) ≤ ((28366863202739730379/28370000000000000000 : ℝ)+2*(80275145723/141850000000000 : ℝ)*(10617/100000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (28366863202739730379/28370000000000000000 : ℝ)+2*(80275145723/141850000000000 : ℝ)*(10617/100000 : ℝ)=(10000095991409339/10000000000000000 : ℝ) by norm_num, show 1+2*(2286867912937713/100000000000000000000 : ℝ)=(50002286867912937713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1758765946913651/10000000000000000000 : ℝ)+(2286867912937713/100000000000000000000 : ℝ) ≤ ((28366863202739730379/28370000000000000000 : ℝ)+(80275145723/141850000000000 : ℝ)*((16291/100000 : ℝ)+(10617/100000 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (28366863202739730379/28370000000000000000 : ℝ)+(80275145723/141850000000000 : ℝ)*((16291/100000 : ℝ)+(10617/100000 : ℝ))=(10000417091992231/10000000000000000 : ℝ) by norm_num, show 1+(1758765946913651/10000000000000000000 : ℝ)+(2286867912937713/100000000000000000000 : ℝ)=(100019874527382074223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1758765946913651/10000000000000000000 : ℝ) ≤ ((28366863202739730379/28370000000000000000 : ℝ)+2*(80275145723/141850000000000 : ℝ)*(16291/100000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (28366863202739730379/28370000000000000000 : ℝ)+2*(80275145723/141850000000000 : ℝ)*(16291/100000 : ℝ)=(10000738192575123/10000000000000000 : ℝ) by norm_num, show 1+2*(1758765946913651/10000000000000000000 : ℝ)=(5001758765946913651/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28366863202739730379/28370000000000000000 : ℝ)*(X 1 0+X 2 0)+(80275145723/141850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (28366863202739730379/28370000000000000000 : ℝ)) (alpha := (80275145723/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28366863202739730379/28370000000000000000 : ℝ)*(X 0 1+X 2 1)+(80275145723/141850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (28366863202739730379/28370000000000000000 : ℝ)) (alpha := (80275145723/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28366863202739730379/28370000000000000000 : ℝ)*(X 0 2+X 1 2)+(80275145723/141850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (16291/100000 : ℝ)) (c := (28366863202739730379/28370000000000000000 : ℝ)) (alpha := (80275145723/141850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-12728659/78125000 : ℝ)*X 0 0+(5450030247/10000000000 : ℝ)*X 0 1+(2591722491/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674522121/5000000000 : ℝ)*X 1 0+(-353309641/2000000000 : ℝ)*X 1 1+(5183445253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133726107/250000000 : ℝ)*X 2 0+(518344499/1000000000 : ℝ)*X 2 1+(-353309701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093851877/5000000000 : ℝ)*X 0 0+(3856950349/10000000000 : ℝ)*X 0 1+(4538859181/10000000000 : ℝ)*X 0 2+(2093851877/5000000000 : ℝ)*X 1 0+(3856950349/10000000000 : ℝ)*X 1 1+(4538859181/10000000000 : ℝ)*X 1 2+(2093851877/5000000000 : ℝ)*X 2 0+(3856950349/10000000000 : ℝ)*X 2 1+(4538859181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-325866691/2000000000 : ℝ)*X 0 0+(324090781/625000000 : ℝ)*X 0 1+(5448001813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527790489/1000000000 : ℝ)*X 1 0+(-187748971/1250000000 : ℝ)*X 1 1+(5448001813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527790489/1000000000 : ℝ)*X 2 0+(5448001813/10000000000 : ℝ)*X 2 1+(-187748971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261741957/625000000 : ℝ)*X 0 0+(4533724247/10000000000 : ℝ)*X 0 1+(1931069491/5000000000 : ℝ)*X 0 2+(261741957/625000000 : ℝ)*X 1 0+(4533724247/10000000000 : ℝ)*X 1 1+(1931069491/5000000000 : ℝ)*X 1 2+(261741957/625000000 : ℝ)*X 2 0+(4533724247/10000000000 : ℝ)*X 2 1+(1931069491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5319825094555976908389829689/709250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (305569093/20000000000000 : ℝ)*(base19) + (1349418981/100000000000000 : ℝ)*(base23) + (74345139/20000000000000 : ℝ)*(upper3) + (54847811/50000000000000 : ℝ)*(upper4) + (461877/100000000000000 : ℝ)*(upper5) + (1304418787042099/50000000000000 : ℝ)*(major0) + (1304418787042099/50000000000000 : ℝ)*(major1) + (1304418787042099/50000000000000 : ℝ)*(major2) + (937792350970307/25000000000000 : ℝ)*(sp0) + (1875592741922203/50000000000000 : ℝ)*(sp1) + (375118566227089/10000000000000 : ℝ)*(sp2) + (733239024891831/50000000000000 : ℝ)*(sp3) + (17607808643/100000000000000 : ℝ)*(sp4) + (4918336849/50000000000000 : ℝ)*(sp7) + (18331098580717/1250000000000 : ℝ)*(f.failure) + (375118701168987/10000000000000 : ℝ)*(f.sum) + (1236319574253/14185000000000000000000000000 : ℝ)*base65 + (28863951308730374479/1418500000000000000000000000000000 : ℝ)*base68 + (21221476481892874479/1418500000000000000000000000000000 : ℝ)*base70 + (16894292957458374479/1418500000000000000000000000000000 : ℝ)*base72 + (24045945917641/7092500000000000000000000000 : ℝ)*base74 + (23845186655758374479/1418500000000000000000000000000000 : ℝ)*base76 + (5584307265196374479/1418500000000000000000000000000000 : ℝ)*base78 + (11931479731966374479/1418500000000000000000000000000000 : ℝ)*base80 + (8126759837793/3546250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (775179/62500000000000000000 : ℝ)*base89 + (775179/62500000000000000000 : ℝ)*base91 + (775179/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1397839327005177649745449929/354625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586944563/100000000000000 : ℝ)*(base19) + (635283899/100000000000000 : ℝ)*(base23) + (184250443/100000000000000 : ℝ)*(lower1) + (82926617/100000000000000 : ℝ)*(upper3) + (679863/3125000000000 : ℝ)*(lower4) + (40870863/50000000000000 : ℝ)*(upper5) + (1324453093756183/50000000000000 : ℝ)*(major0) + (1324453093756183/50000000000000 : ℝ)*(major1) + (1324453093756183/50000000000000 : ℝ)*(major2) + (264089349/50000000000000 : ℝ)*(sp2) + (1904400431823243/50000000000000 : ℝ)*(sp4) + (1904400138350961/50000000000000 : ℝ)*(sp5) + (238049981261493/6250000000000 : ℝ)*(sp6) + (372252844996729/25000000000000 : ℝ)*(sp7) + (372252844996729/25000000000000 : ℝ)*(f.failure) + (1904400431823243/50000000000000 : ℝ)*(f.sum) + (24036676145383/7092500000000000000000000000 : ℝ)*base65 + (17651997315447983357/1418500000000000000000000000000000 : ℝ)*base67 + (10413957595809016643/1418500000000000000000000000000000 : ℝ)*base70 + (84841418611163983357/1418500000000000000000000000000000 : ℝ)*base71 + (7676953577297/1773125000000000000000000000 : ℝ)*base73 + (16257380897832983357/1418500000000000000000000000000000 : ℝ)*base75 + (10323413177333983357/1418500000000000000000000000000000 : ℝ)*base77 + (6672973410449983357/1418500000000000000000000000000000 : ℝ)*base79 + (8235902683603/7092500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10500977/1250000000000000000000 : ℝ)*base90 + (10500977/1250000000000000000000 : ℝ)*base92 + (10500977/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1641_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3257/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1641_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1641_box_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-171001753/1250000000 : ℝ)*x 0 + (5410288169/10000000000 : ℝ)*x 1 + (5410287837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171001753/1250000000 : ℝ)^4883 ≤ (4034771724477/50000000000000 : ℝ)^3859 := by
    have hnat : (171001753 : ℕ)^4883*50000000000000^3859 ≤ 4034771724477^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171001753 1250000000 4034771724477 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410288169/10000000000 : ℝ)^4883 ≤ (45965230053807/100000000000000 : ℝ)^3859 := by
    have hnat : (5410288169 : ℕ)^4883*100000000000000^3859 ≤ 45965230053807^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410288169 10000000000 45965230053807 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410287837/10000000000 : ℝ)^4883 ≤ (1436413327647/3125000000000 : ℝ)^3859 := by
    have hnat : (5410287837 : ℕ)^4883*3125000000000^3859 ≤ 1436413327647^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410287837 10000000000 1436413327647 3125000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-171001753/1250000000 : ℝ), (5410288169/10000000000 : ℝ), (5410287837/10000000000 : ℝ)] ![(4034771724477/50000000000000 : ℝ), (45965230053807/100000000000000 : ℝ), (1436413327647/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-171001753/1250000000 : ℝ)|^4883 ≤ (4034771724477/50000000000000 : ℝ)^3859
        have hw : |(-171001753/1250000000 : ℝ)|=(171001753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410288169/10000000000 : ℝ)|^4883 ≤ (45965230053807/100000000000000 : ℝ)^3859
        have hw : |(5410288169/10000000000 : ℝ)|=(5410288169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410287837/10000000000 : ℝ)|^4883 ≤ (1436413327647/3125000000000 : ℝ)^3859
        have hw : |(5410287837/10000000000 : ℝ)|=(5410287837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210047491/400000000 : ℝ)*x 0 + (-795799251/5000000000 : ℝ)*x 1 + (2705143863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210047491/400000000 : ℝ)^4883 ≤ (22130784056799/50000000000000 : ℝ)^3859 := by
    have hnat : (210047491 : ℕ)^4883*50000000000000^3859 ≤ 22130784056799^3859*400000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210047491 400000000 22130784056799 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795799251/5000000000 : ℝ)^4883 ≤ (1954641315761/20000000000000 : ℝ)^3859 := by
    have hnat : (795799251 : ℕ)^4883*20000000000000^3859 ≤ 1954641315761^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795799251 5000000000 1954641315761 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705143863/5000000000 : ℝ)^4883 ≤ (2298261264571/5000000000000 : ℝ)^3859 := by
    have hnat : (2705143863 : ℕ)^4883*5000000000000^3859 ≤ 2298261264571^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705143863 5000000000 2298261264571 5000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210047491/400000000 : ℝ), (-795799251/5000000000 : ℝ), (2705143863/5000000000 : ℝ)] ![(22130784056799/50000000000000 : ℝ), (1954641315761/20000000000000 : ℝ), (2298261264571/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210047491/400000000 : ℝ)|^4883 ≤ (22130784056799/50000000000000 : ℝ)^3859
        have hw : |(210047491/400000000 : ℝ)|=(210047491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-795799251/5000000000 : ℝ)|^4883 ≤ (1954641315761/20000000000000 : ℝ)^3859
        have hw : |(-795799251/5000000000 : ℝ)|=(795799251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705143863/5000000000 : ℝ)|^4883 ≤ (2298261264571/5000000000000 : ℝ)^3859
        have hw : |(2705143863/5000000000 : ℝ)|=(2705143863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312796771/2500000000 : ℝ)*x 0 + (2705144013/5000000000 : ℝ)*x 1 + (-31831967/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312796771/2500000000 : ℝ)^4883 ≤ (5532695759561/12500000000000 : ℝ)^3859 := by
    have hnat : (1312796771 : ℕ)^4883*12500000000000^3859 ≤ 5532695759561^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312796771 2500000000 5532695759561 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705144013/5000000000 : ℝ)^4883 ≤ (45965228516513/100000000000000 : ℝ)^3859 := by
    have hnat : (2705144013 : ℕ)^4883*100000000000000^3859 ≤ 45965228516513^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705144013 5000000000 45965228516513 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31831967/200000000 : ℝ)^4883 ≤ (488660269889/5000000000000 : ℝ)^3859 := by
    have hnat : (31831967 : ℕ)^4883*5000000000000^3859 ≤ 488660269889^3859*200000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31831967 200000000 488660269889 5000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312796771/2500000000 : ℝ), (2705144013/5000000000 : ℝ), (-31831967/200000000 : ℝ)] ![(5532695759561/12500000000000 : ℝ), (45965228516513/100000000000000 : ℝ), (488660269889/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312796771/2500000000 : ℝ)|^4883 ≤ (5532695759561/12500000000000 : ℝ)^3859
        have hw : |(1312796771/2500000000 : ℝ)|=(1312796771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705144013/5000000000 : ℝ)|^4883 ≤ (45965228516513/100000000000000 : ℝ)^3859
        have hw : |(2705144013/5000000000 : ℝ)|=(2705144013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31831967/200000000 : ℝ)|^4883 ≤ (488660269889/5000000000000 : ℝ)^3859
        have hw : |(-31831967/200000000 : ℝ)|=(31831967/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4465121351/10000000000 : ℝ)*x 0 + (4061167389/10000000000 : ℝ)*x 1 + (2030583649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465121351/10000000000 : ℝ)^4883 ≤ (36050826149371/100000000000000 : ℝ)^3859 := by
    have hnat : (4465121351 : ℕ)^4883*100000000000000^3859 ≤ 36050826149371^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465121351 10000000000 36050826149371 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4061167389/10000000000 : ℝ)^4883 ≤ (3996823420851/12500000000000 : ℝ)^3859 := by
    have hnat : (4061167389 : ℕ)^4883*12500000000000^3859 ≤ 3996823420851^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4061167389 10000000000 3996823420851 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030583649/5000000000 : ℝ)^4883 ≤ (1278983458409/4000000000000 : ℝ)^3859 := by
    have hnat : (2030583649 : ℕ)^4883*4000000000000^3859 ≤ 1278983458409^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030583649 5000000000 1278983458409 4000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4465121351/10000000000 : ℝ), (4061167389/10000000000 : ℝ), (2030583649/5000000000 : ℝ)] ![(36050826149371/100000000000000 : ℝ), (3996823420851/12500000000000 : ℝ), (1278983458409/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4465121351/10000000000 : ℝ)|^4883 ≤ (36050826149371/100000000000000 : ℝ)^3859
        have hw : |(4465121351/10000000000 : ℝ)|=(4465121351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4061167389/10000000000 : ℝ)|^4883 ≤ (3996823420851/12500000000000 : ℝ)^3859
        have hw : |(4061167389/10000000000 : ℝ)|=(4061167389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2030583649/5000000000 : ℝ)|^4883 ≤ (1278983458409/4000000000000 : ℝ)^3859
        have hw : |(2030583649/5000000000 : ℝ)|=(2030583649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901160177/10000000000 : ℝ)*x 0 + (162983809/312500000 : ℝ)*x 1 + (5215481791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901160177/10000000000 : ℝ)^4883 ≤ (122378081911/1000000000000 : ℝ)^3859 := by
    have hnat : (1901160177 : ℕ)^4883*1000000000000^3859 ≤ 122378081911^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901160177 10000000000 122378081911 1000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162983809/312500000 : ℝ)^4883 ≤ (109702741041/250000000000 : ℝ)^3859 := by
    have hnat : (162983809 : ℕ)^4883*250000000000^3859 ≤ 109702741041^3859*312500000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162983809 312500000 109702741041 250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215481791/10000000000 : ℝ)^4883 ≤ (21940547691859/50000000000000 : ℝ)^3859 := by
    have hnat : (5215481791 : ℕ)^4883*50000000000000^3859 ≤ 21940547691859^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215481791 10000000000 21940547691859 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901160177/10000000000 : ℝ), (162983809/312500000 : ℝ), (5215481791/10000000000 : ℝ)] ![(122378081911/1000000000000 : ℝ), (109702741041/250000000000 : ℝ), (21940547691859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901160177/10000000000 : ℝ)|^4883 ≤ (122378081911/1000000000000 : ℝ)^3859
        have hw : |(-1901160177/10000000000 : ℝ)|=(1901160177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162983809/312500000 : ℝ)|^4883 ≤ (109702741041/250000000000 : ℝ)^3859
        have hw : |(162983809/312500000 : ℝ)|=(162983809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215481791/10000000000 : ℝ)|^4883 ≤ (21940547691859/50000000000000 : ℝ)^3859
        have hw : |(5215481791/10000000000 : ℝ)|=(5215481791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346265131/2500000000 : ℝ)*x 0 + (-1674877293/10000000000 : ℝ)*x 1 + (5215481907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346265131/2500000000 : ℝ)^4883 ≤ (22847096513011/50000000000000 : ℝ)^3859 := by
    have hnat : (1346265131 : ℕ)^4883*50000000000000^3859 ≤ 22847096513011^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346265131 2500000000 22847096513011 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674877293/10000000000 : ℝ)^4883 ≤ (2084942068553/20000000000000 : ℝ)^3859 := by
    have hnat : (1674877293 : ℕ)^4883*20000000000000^3859 ≤ 2084942068553^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674877293 10000000000 2084942068553 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215481907/10000000000 : ℝ)^4883 ≤ (21940548309339/50000000000000 : ℝ)^3859 := by
    have hnat : (5215481907 : ℕ)^4883*50000000000000^3859 ≤ 21940548309339^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215481907 10000000000 21940548309339 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346265131/2500000000 : ℝ), (-1674877293/10000000000 : ℝ), (5215481907/10000000000 : ℝ)] ![(22847096513011/50000000000000 : ℝ), (2084942068553/20000000000000 : ℝ), (21940548309339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346265131/2500000000 : ℝ)|^4883 ≤ (22847096513011/50000000000000 : ℝ)^3859
        have hw : |(1346265131/2500000000 : ℝ)|=(1346265131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1674877293/10000000000 : ℝ)|^4883 ≤ (2084942068553/20000000000000 : ℝ)^3859
        have hw : |(-1674877293/10000000000 : ℝ)|=(1674877293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215481907/10000000000 : ℝ)|^4883 ≤ (21940548309339/50000000000000 : ℝ)^3859
        have hw : |(5215481907/10000000000 : ℝ)|=(5215481907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107701211/200000000 : ℝ)*x 0 + (5215482061/10000000000 : ℝ)*x 1 + (-33497541/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107701211/200000000 : ℝ)^4883 ≤ (45694193305183/100000000000000 : ℝ)^3859 := by
    have hnat : (107701211 : ℕ)^4883*100000000000000^3859 ≤ 45694193305183^3859*200000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107701211 200000000 45694193305183 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215482061/10000000000 : ℝ)^4883 ≤ (21940549129097/50000000000000 : ℝ)^3859 := by
    have hnat : (5215482061 : ℕ)^4883*50000000000000^3859 ≤ 21940549129097^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215482061 10000000000 21940549129097 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33497541/200000000 : ℝ)^4883 ≤ (10424708428953/100000000000000 : ℝ)^3859 := by
    have hnat : (33497541 : ℕ)^4883*100000000000000^3859 ≤ 10424708428953^3859*200000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33497541 200000000 10424708428953 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107701211/200000000 : ℝ), (5215482061/10000000000 : ℝ), (-33497541/200000000 : ℝ)] ![(45694193305183/100000000000000 : ℝ), (21940549129097/50000000000000 : ℝ), (10424708428953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107701211/200000000 : ℝ)|^4883 ≤ (45694193305183/100000000000000 : ℝ)^3859
        have hw : |(107701211/200000000 : ℝ)|=(107701211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215482061/10000000000 : ℝ)|^4883 ≤ (21940549129097/50000000000000 : ℝ)^3859
        have hw : |(5215482061/10000000000 : ℝ)|=(5215482061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33497541/200000000 : ℝ)|^4883 ≤ (10424708428953/100000000000000 : ℝ)^3859
        have hw : |(-33497541/200000000 : ℝ)|=(33497541/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1951957513/5000000000 : ℝ)*x 0 + (4341441651/10000000000 : ℝ)*x 1 + (27134011/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951957513/5000000000 : ℝ)^4883 ≤ (3802011879937/12500000000000 : ℝ)^3859 := by
    have hnat : (1951957513 : ℕ)^4883*12500000000000^3859 ≤ 3802011879937^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951957513 5000000000 3802011879937 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4341441651/10000000000 : ℝ)^4883 ≤ (6958390384521/20000000000000 : ℝ)^3859 := by
    have hnat : (4341441651 : ℕ)^4883*20000000000000^3859 ≤ 6958390384521^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341441651 10000000000 6958390384521 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27134011/62500000 : ℝ)^4883 ≤ (34791953027913/100000000000000 : ℝ)^3859 := by
    have hnat : (27134011 : ℕ)^4883*100000000000000^3859 ≤ 34791953027913^3859*62500000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27134011 62500000 34791953027913 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1951957513/5000000000 : ℝ), (4341441651/10000000000 : ℝ), (27134011/62500000 : ℝ)] ![(3802011879937/12500000000000 : ℝ), (6958390384521/20000000000000 : ℝ), (34791953027913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1951957513/5000000000 : ℝ)|^4883 ≤ (3802011879937/12500000000000 : ℝ)^3859
        have hw : |(1951957513/5000000000 : ℝ)|=(1951957513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4341441651/10000000000 : ℝ)|^4883 ≤ (6958390384521/20000000000000 : ℝ)^3859
        have hw : |(4341441651/10000000000 : ℝ)|=(4341441651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27134011/62500000 : ℝ)|^4883 ≤ (34791953027913/100000000000000 : ℝ)^3859
        have hw : |(27134011/62500000 : ℝ)|=(27134011/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_8 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111719343/625000000 : ℝ)*x 0 + (5075590487/10000000000 : ℝ)*x 1 + (5439855479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111719343/625000000 : ℝ)^4883 ≤ (2263912680163/20000000000000 : ℝ)^3859 := by
    have hnat : (111719343 : ℕ)^4883*20000000000000^3859 ≤ 2263912680163^3859*625000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111719343 625000000 2263912680163 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075590487/10000000000 : ℝ)^4883 ≤ (42397118615533/100000000000000 : ℝ)^3859 := by
    have hnat : (5075590487 : ℕ)^4883*100000000000000^3859 ≤ 42397118615533^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075590487 10000000000 42397118615533 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439855479/10000000000 : ℝ)^4883 ≤ (5785414745731/12500000000000 : ℝ)^3859 := by
    have hnat : (5439855479 : ℕ)^4883*12500000000000^3859 ≤ 5785414745731^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439855479 10000000000 5785414745731 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111719343/625000000 : ℝ), (5075590487/10000000000 : ℝ), (5439855479/10000000000 : ℝ)] ![(2263912680163/20000000000000 : ℝ), (42397118615533/100000000000000 : ℝ), (5785414745731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111719343/625000000 : ℝ)|^4883 ≤ (2263912680163/20000000000000 : ℝ)^3859
        have hw : |(-111719343/625000000 : ℝ)|=(111719343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075590487/10000000000 : ℝ)|^4883 ≤ (42397118615533/100000000000000 : ℝ)^3859
        have hw : |(5075590487/10000000000 : ℝ)|=(5075590487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439855479/10000000000 : ℝ)|^4883 ≤ (5785414745731/12500000000000 : ℝ)^3859
        have hw : |(5439855479/10000000000 : ℝ)|=(5439855479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_9 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230868099/10000000000 : ℝ)*x 0 + (-157852297/1000000000 : ℝ)*x 1 + (2719927497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230868099/10000000000 : ℝ)^4883 ≤ (44044965298097/100000000000000 : ℝ)^3859 := by
    have hnat : (5230868099 : ℕ)^4883*100000000000000^3859 ≤ 44044965298097^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230868099 10000000000 44044965298097 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157852297/1000000000 : ℝ)^4883 ≤ (120896524337/1250000000000 : ℝ)^3859 := by
    have hnat : (157852297 : ℕ)^4883*1250000000000^3859 ≤ 120896524337^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157852297 1000000000 120896524337 1250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719927497/5000000000 : ℝ)^4883 ≤ (23141656372201/50000000000000 : ℝ)^3859 := by
    have hnat : (2719927497 : ℕ)^4883*50000000000000^3859 ≤ 23141656372201^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719927497 5000000000 23141656372201 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230868099/10000000000 : ℝ), (-157852297/1000000000 : ℝ), (2719927497/5000000000 : ℝ)] ![(44044965298097/100000000000000 : ℝ), (120896524337/1250000000000 : ℝ), (23141656372201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230868099/10000000000 : ℝ)|^4883 ≤ (44044965298097/100000000000000 : ℝ)^3859
        have hw : |(5230868099/10000000000 : ℝ)|=(5230868099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157852297/1000000000 : ℝ)|^4883 ≤ (120896524337/1250000000000 : ℝ)^3859
        have hw : |(-157852297/1000000000 : ℝ)|=(157852297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719927497/5000000000 : ℝ)|^4883 ≤ (23141656372201/50000000000000 : ℝ)^3859
        have hw : |(2719927497/5000000000 : ℝ)|=(2719927497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_10 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615434329/5000000000 : ℝ)*x 0 + (339990937/625000000 : ℝ)*x 1 + (-394630551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615434329/5000000000 : ℝ)^4883 ≤ (22022485626991/50000000000000 : ℝ)^3859 := by
    have hnat : (2615434329 : ℕ)^4883*50000000000000^3859 ≤ 22022485626991^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615434329 5000000000 22022485626991 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339990937/625000000 : ℝ)^4883 ≤ (46283312722871/100000000000000 : ℝ)^3859 := by
    have hnat : (339990937 : ℕ)^4883*100000000000000^3859 ≤ 46283312722871^3859*625000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339990937 625000000 46283312722871 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394630551/2500000000 : ℝ)^4883 ≤ (967171600823/10000000000000 : ℝ)^3859 := by
    have hnat : (394630551 : ℕ)^4883*10000000000000^3859 ≤ 967171600823^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394630551 2500000000 967171600823 10000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615434329/5000000000 : ℝ), (339990937/625000000 : ℝ), (-394630551/2500000000 : ℝ)] ![(22022485626991/50000000000000 : ℝ), (46283312722871/100000000000000 : ℝ), (967171600823/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615434329/5000000000 : ℝ)|^4883 ≤ (22022485626991/50000000000000 : ℝ)^3859
        have hw : |(2615434329/5000000000 : ℝ)|=(2615434329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339990937/625000000 : ℝ)|^4883 ≤ (46283312722871/100000000000000 : ℝ)^3859
        have hw : |(339990937/625000000 : ℝ)|=(339990937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394630551/2500000000 : ℝ)|^4883 ≤ (967171600823/10000000000000 : ℝ)^3859
        have hw : |(-394630551/2500000000 : ℝ)|=(394630551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_11 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4547918073/10000000000 : ℝ)*x 0 + (1004637687/2500000000 : ℝ)*x 1 + (2009275249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4547918073/10000000000 : ℝ)^4883 ≤ (18449387243457/50000000000000 : ℝ)^3859 := by
    have hnat : (4547918073 : ℕ)^4883*50000000000000^3859 ≤ 18449387243457^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547918073 10000000000 18449387243457 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004637687/2500000000 : ℝ)^4883 ≤ (31550613995417/100000000000000 : ℝ)^3859 := by
    have hnat : (1004637687 : ℕ)^4883*100000000000000^3859 ≤ 31550613995417^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004637687 2500000000 31550613995417 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009275249/5000000000 : ℝ)^4883 ≤ (31550611511767/100000000000000 : ℝ)^3859 := by
    have hnat : (2009275249 : ℕ)^4883*100000000000000^3859 ≤ 31550611511767^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009275249 5000000000 31550611511767 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4547918073/10000000000 : ℝ), (1004637687/2500000000 : ℝ), (2009275249/5000000000 : ℝ)] ![(18449387243457/50000000000000 : ℝ), (31550613995417/100000000000000 : ℝ), (31550611511767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4547918073/10000000000 : ℝ)|^4883 ≤ (18449387243457/50000000000000 : ℝ)^3859
        have hw : |(4547918073/10000000000 : ℝ)|=(4547918073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004637687/2500000000 : ℝ)|^4883 ≤ (31550613995417/100000000000000 : ℝ)^3859
        have hw : |(1004637687/2500000000 : ℝ)|=(1004637687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2009275249/5000000000 : ℝ)|^4883 ≤ (31550611511767/100000000000000 : ℝ)^3859
        have hw : |(2009275249/5000000000 : ℝ)|=(2009275249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_12 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-740006131/5000000000 : ℝ)*x 0 + (1108952161/2000000000 : ℝ)*x 1 + (1039128873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740006131/5000000000 : ℝ)^4883 ≤ (8914400237667/100000000000000 : ℝ)^3859 := by
    have hnat : (740006131 : ℕ)^4883*100000000000000^3859 ≤ 8914400237667^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740006131 5000000000 8914400237667 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108952161/2000000000 : ℝ)^4883 ≤ (1896623642677/4000000000000 : ℝ)^3859 := by
    have hnat : (1108952161 : ℕ)^4883*4000000000000^3859 ≤ 1896623642677^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108952161 2000000000 1896623642677 4000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039128873/2000000000 : ℝ)^4883 ≤ (8734001737021/20000000000000 : ℝ)^3859 := by
    have hnat : (1039128873 : ℕ)^4883*20000000000000^3859 ≤ 8734001737021^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039128873 2000000000 8734001737021 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-740006131/5000000000 : ℝ), (1108952161/2000000000 : ℝ), (1039128873/2000000000 : ℝ)] ![(8914400237667/100000000000000 : ℝ), (1896623642677/4000000000000 : ℝ), (8734001737021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-740006131/5000000000 : ℝ)|^4883 ≤ (8914400237667/100000000000000 : ℝ)^3859
        have hw : |(-740006131/5000000000 : ℝ)|=(740006131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108952161/2000000000 : ℝ)|^4883 ≤ (1896623642677/4000000000000 : ℝ)^3859
        have hw : |(1108952161/2000000000 : ℝ)|=(1108952161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039128873/2000000000 : ℝ)|^4883 ≤ (8734001737021/20000000000000 : ℝ)^3859
        have hw : |(1039128873/2000000000 : ℝ)|=(1039128873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_13 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539870227/1000000000 : ℝ)*x 0 + (-841535173/5000000000 : ℝ)*x 1 + (5195644279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539870227/1000000000 : ℝ)^4883 ≤ (22920356727469/50000000000000 : ℝ)^3859 := by
    have hnat : (539870227 : ℕ)^4883*50000000000000^3859 ≤ 22920356727469^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539870227 1000000000 22920356727469 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841535173/5000000000 : ℝ)^4883 ≤ (2622319690329/25000000000000 : ℝ)^3859 := by
    have hnat : (841535173 : ℕ)^4883*25000000000000^3859 ≤ 2622319690329^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841535173 5000000000 2622319690329 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195644279/10000000000 : ℝ)^4883 ≤ (43670007770457/100000000000000 : ℝ)^3859 := by
    have hnat : (5195644279 : ℕ)^4883*100000000000000^3859 ≤ 43670007770457^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195644279 10000000000 43670007770457 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539870227/1000000000 : ℝ), (-841535173/5000000000 : ℝ), (5195644279/10000000000 : ℝ)] ![(22920356727469/50000000000000 : ℝ), (2622319690329/25000000000000 : ℝ), (43670007770457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539870227/1000000000 : ℝ)|^4883 ≤ (22920356727469/50000000000000 : ℝ)^3859
        have hw : |(539870227/1000000000 : ℝ)|=(539870227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-841535173/5000000000 : ℝ)|^4883 ≤ (2622319690329/25000000000000 : ℝ)^3859
        have hw : |(-841535173/5000000000 : ℝ)|=(841535173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195644279/10000000000 : ℝ)|^4883 ≤ (43670007770457/100000000000000 : ℝ)^3859
        have hw : |(5195644279/10000000000 : ℝ)|=(5195644279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_14 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398702537/10000000000 : ℝ)*x 0 + (2597821951/5000000000 : ℝ)*x 1 + (-168307049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398702537/10000000000 : ℝ)^4883 ≤ (22920358161819/50000000000000 : ℝ)^3859 := by
    have hnat : (5398702537 : ℕ)^4883*50000000000000^3859 ≤ 22920358161819^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398702537 10000000000 22920358161819 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597821951/5000000000 : ℝ)^4883 ≤ (43670003760893/100000000000000 : ℝ)^3859 := by
    have hnat : (2597821951 : ℕ)^4883*100000000000000^3859 ≤ 43670003760893^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597821951 5000000000 43670003760893 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168307049/1000000000 : ℝ)^4883 ≤ (163894998389/1562500000000 : ℝ)^3859 := by
    have hnat : (168307049 : ℕ)^4883*1562500000000^3859 ≤ 163894998389^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168307049 1000000000 163894998389 1562500000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398702537/10000000000 : ℝ), (2597821951/5000000000 : ℝ), (-168307049/1000000000 : ℝ)] ![(22920358161819/50000000000000 : ℝ), (43670003760893/100000000000000 : ℝ), (163894998389/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398702537/10000000000 : ℝ)|^4883 ≤ (22920358161819/50000000000000 : ℝ)^3859
        have hw : |(5398702537/10000000000 : ℝ)|=(5398702537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597821951/5000000000 : ℝ)|^4883 ≤ (43670003760893/100000000000000 : ℝ)^3859
        have hw : |(2597821951/5000000000 : ℝ)|=(2597821951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168307049/1000000000 : ℝ)|^4883 ≤ (163894998389/1562500000000 : ℝ)^3859
        have hw : |(-168307049/1000000000 : ℝ)|=(168307049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_box_15 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3845138549/10000000000 : ℝ)*x 0 + (436993079/1000000000 : ℝ)*x 1 + (2184965681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3845138549/10000000000 : ℝ)^4883 ≤ (29837803314923/100000000000000 : ℝ)^3859 := by
    have hnat : (3845138549 : ℕ)^4883*100000000000000^3859 ≤ 29837803314923^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845138549 10000000000 29837803314923 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436993079/1000000000 : ℝ)^4883 ≤ (17540547714017/50000000000000 : ℝ)^3859 := by
    have hnat : (436993079 : ℕ)^4883*50000000000000^3859 ≤ 17540547714017^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436993079 1000000000 17540547714017 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184965681/5000000000 : ℝ)^4883 ≤ (35081101238441/100000000000000 : ℝ)^3859 := by
    have hnat : (2184965681 : ℕ)^4883*100000000000000^3859 ≤ 35081101238441^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184965681 5000000000 35081101238441 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3845138549/10000000000 : ℝ), (436993079/1000000000 : ℝ), (2184965681/5000000000 : ℝ)] ![(29837803314923/100000000000000 : ℝ), (17540547714017/50000000000000 : ℝ), (35081101238441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3845138549/10000000000 : ℝ)|^4883 ≤ (29837803314923/100000000000000 : ℝ)^3859
        have hw : |(3845138549/10000000000 : ℝ)|=(3845138549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(436993079/1000000000 : ℝ)|^4883 ≤ (17540547714017/50000000000000 : ℝ)^3859
        have hw : |(436993079/1000000000 : ℝ)|=(436993079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184965681/5000000000 : ℝ)|^4883 ≤ (35081101238441/100000000000000 : ℝ)^3859
        have hw : |(2184965681/5000000000 : ℝ)|=(2184965681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3257/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65031/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58529/100000 : ℝ) ∧ (81031/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17627/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3257/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3257/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3257/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3257/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3257/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3257/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5311/50000 : ℝ) ^ (4879/1024 : ℝ) ≤ (71625122315717/3125000000000000000 : ℝ) := by
    have hpowers : (5311/50000 : ℝ)^4879 ≤ (71625122315717/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5311 : ℕ)^4879*3125000000000000000^1024 ≤ 71625122315717^1024*50000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5311 50000 71625122315717 3125000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5311/50000 : ℝ)) (X := (71625122315717/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3257/20000 : ℝ) ^ (4879/1024 : ℝ) ≤ (2194602194283877/12500000000000000000 : ℝ) := by
    have hpowers : (3257/20000 : ℝ)^4879 ≤ (2194602194283877/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3257 : ℕ)^4879*12500000000000000000^1024 ≤ 2194602194283877^1024*20000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3257 20000 2194602194283877 12500000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3257/20000 : ℝ)) (X := (2194602194283877/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562571625122315717/1562500000000000000 : ℝ) ≤ (10000096206989373/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (1562571625122315717/1562500000000000000 : ℝ)^1024 ≤ (10000096206989373/10000000000000000 : ℝ)^4879 := by
      have hnat : (1562571625122315717 : ℕ)^1024*10000000000000000^4879 ≤ 10000096206989373^4879*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562571625122315717 1562500000000000000 10000096206989373 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000096206989373/10000000000000000 : ℝ)) (X := (1562571625122315717/1562500000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500496220536709349/2500000000000000000 : ℝ) ≤ (2500104138140887/2500000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (2500496220536709349/2500000000000000000 : ℝ)^1024 ≤ (2500104138140887/2500000000000000 : ℝ)^4879 := by
      have hnat : (2500496220536709349 : ℕ)^1024*2500000000000000^4879 ≤ 2500104138140887^4879*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500496220536709349 2500000000000000000 2500104138140887 2500000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500104138140887/2500000000000000 : ℝ)) (X := (2500496220536709349/2500000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252194602194283877/6250000000000000000 : ℝ) ≤ (10000736898137723/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (6252194602194283877/6250000000000000000 : ℝ)^1024 ≤ (10000736898137723/10000000000000000 : ℝ)^4879 := by
      have hnat : (6252194602194283877 : ℕ)^1024*10000000000000000^4879 ≤ 10000736898137723^4879*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252194602194283877 6250000000000000000 10000736898137723 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000736898137723/10000000000000000 : ℝ)) (X := (6252194602194283877/6250000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(71625122315717/3125000000000000000 : ℝ) ≤ ((56623739398803045599/56630000000000000000 : ℝ)+2*(12813822967/22652000000000 : ℝ)*(5311/50000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (56623739398803045599/56630000000000000000 : ℝ)+2*(12813822967/22652000000000 : ℝ)*(5311/50000 : ℝ)=(10000096206989373/10000000000000000 : ℝ) by norm_num, show 1+2*(71625122315717/3125000000000000000 : ℝ)=(1562571625122315717/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2194602194283877/12500000000000000000 : ℝ)+(71625122315717/3125000000000000000 : ℝ) ≤ ((56623739398803045599/56630000000000000000 : ℝ)+(12813822967/22652000000000 : ℝ)*((3257/20000 : ℝ)+(5311/50000 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (56623739398803045599/56630000000000000000 : ℝ)+(12813822967/22652000000000 : ℝ)*((3257/20000 : ℝ)+(5311/50000 : ℝ))=(2500104138140887/2500000000000000 : ℝ) by norm_num, show 1+(2194602194283877/12500000000000000000 : ℝ)+(71625122315717/3125000000000000000 : ℝ)=(2500496220536709349/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2194602194283877/12500000000000000000 : ℝ) ≤ ((56623739398803045599/56630000000000000000 : ℝ)+2*(12813822967/22652000000000 : ℝ)*(3257/20000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (56623739398803045599/56630000000000000000 : ℝ)+2*(12813822967/22652000000000 : ℝ)*(3257/20000 : ℝ)=(10000736898137723/10000000000000000 : ℝ) by norm_num, show 1+2*(2194602194283877/12500000000000000000 : ℝ)=(6252194602194283877/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56623739398803045599/56630000000000000000 : ℝ)*(X 1 0+X 2 0)+(12813822967/22652000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (3257/20000 : ℝ)) (c := (56623739398803045599/56630000000000000000 : ℝ)) (alpha := (12813822967/22652000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56623739398803045599/56630000000000000000 : ℝ)*(X 0 1+X 2 1)+(12813822967/22652000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (3257/20000 : ℝ)) (c := (56623739398803045599/56630000000000000000 : ℝ)) (alpha := (12813822967/22652000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56623739398803045599/56630000000000000000 : ℝ)*(X 0 2+X 1 2)+(12813822967/22652000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (3257/20000 : ℝ)) (c := (56623739398803045599/56630000000000000000 : ℝ)) (alpha := (12813822967/22652000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-171001753/1250000000 : ℝ)*X 0 0+(5410288169/10000000000 : ℝ)*X 0 1+(5410287837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((210047491/400000000 : ℝ)*X 1 0+(-795799251/5000000000 : ℝ)*X 1 1+(2705143863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1312796771/2500000000 : ℝ)*X 2 0+(2705144013/5000000000 : ℝ)*X 2 1+(-31831967/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4465121351/10000000000 : ℝ)*X 0 0+(4061167389/10000000000 : ℝ)*X 0 1+(2030583649/5000000000 : ℝ)*X 0 2+(4465121351/10000000000 : ℝ)*X 1 0+(4061167389/10000000000 : ℝ)*X 1 1+(2030583649/5000000000 : ℝ)*X 1 2+(4465121351/10000000000 : ℝ)*X 2 0+(4061167389/10000000000 : ℝ)*X 2 1+(2030583649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1901160177/10000000000 : ℝ)*X 0 0+(162983809/312500000 : ℝ)*X 0 1+(5215481791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346265131/2500000000 : ℝ)*X 1 0+(-1674877293/10000000000 : ℝ)*X 1 1+(5215481907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((107701211/200000000 : ℝ)*X 2 0+(5215482061/10000000000 : ℝ)*X 2 1+(-33497541/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1951957513/5000000000 : ℝ)*X 0 0+(4341441651/10000000000 : ℝ)*X 0 1+(27134011/62500000 : ℝ)*X 0 2+(1951957513/5000000000 : ℝ)*X 1 0+(4341441651/10000000000 : ℝ)*X 1 1+(27134011/62500000 : ℝ)*X 1 2+(1951957513/5000000000 : ℝ)*X 2 0+(4341441651/10000000000 : ℝ)*X 2 1+(27134011/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-111719343/625000000 : ℝ)*X 0 0+(5075590487/10000000000 : ℝ)*X 0 1+(5439855479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230868099/10000000000 : ℝ)*X 1 0+(-157852297/1000000000 : ℝ)*X 1 1+(2719927497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615434329/5000000000 : ℝ)*X 2 0+(339990937/625000000 : ℝ)*X 2 1+(-394630551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4547918073/10000000000 : ℝ)*X 0 0+(1004637687/2500000000 : ℝ)*X 0 1+(2009275249/5000000000 : ℝ)*X 0 2+(4547918073/10000000000 : ℝ)*X 1 0+(1004637687/2500000000 : ℝ)*X 1 1+(2009275249/5000000000 : ℝ)*X 1 2+(4547918073/10000000000 : ℝ)*X 2 0+(1004637687/2500000000 : ℝ)*X 2 1+(2009275249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-740006131/5000000000 : ℝ)*X 0 0+(1108952161/2000000000 : ℝ)*X 0 1+(1039128873/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((539870227/1000000000 : ℝ)*X 1 0+(-841535173/5000000000 : ℝ)*X 1 1+(5195644279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5398702537/10000000000 : ℝ)*X 2 0+(2597821951/5000000000 : ℝ)*X 2 1+(-168307049/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3845138549/10000000000 : ℝ)*X 0 0+(436993079/1000000000 : ℝ)*X 0 1+(2184965681/5000000000 : ℝ)*X 0 2+(3845138549/10000000000 : ℝ)*X 1 0+(436993079/1000000000 : ℝ)*X 1 1+(2184965681/5000000000 : ℝ)*X 1 2+(3845138549/10000000000 : ℝ)*X 2 0+(436993079/1000000000 : ℝ)*X 2 1+(2184965681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65031/100000 : ℝ) ≤ (-920639119051447215737454319853997/1415750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8800203/100000000000000 : ℝ)*(lower1) + (3805107/10000000000000 : ℝ)*(lower2) + (49739437/100000000000000 : ℝ)*(lower3) + (5391719/100000000000000 : ℝ)*(lower5) + (870887739737601/50000000000000 : ℝ)*(major0) + (870887739737601/50000000000000 : ℝ)*(major1) + (870887739737601/50000000000000 : ℝ)*(major2) + (252613299749667/10000000000000 : ℝ)*(sp4) + (1263060104325273/50000000000000 : ℝ)*(sp5) + (315762141350619/12500000000000 : ℝ)*(sp6) + (489546123329563/50000000000000 : ℝ)*(sp7) + (14699519/800000000000 : ℝ)*(sp8) + (7313142999/50000000000000 : ℝ)*(sp13) + (37704131593/100000000000000 : ℝ)*(sp14) + (489546123329563/50000000000000 : ℝ)*(f.failure) + (78941713591767/3125000000000 : ℝ)*(f.sum) + (6971839242713/1415750000000000000000000000 : ℝ)*base65 + (6671424201481132001/2831500000000000000000000000000000 : ℝ)*base68 + (14833007032617132001/2831500000000000000000000000000000 : ℝ)*base70 + (21347260090855367999/2831500000000000000000000000000000 : ℝ)*base71 + (325013425519/113260000000000000000000000 : ℝ)*base74 + (2849100083759367999/2831500000000000000000000000000000 : ℝ)*base75 + (5424791350729867999/2831500000000000000000000000000000 : ℝ)*base77 + (939138488119367999/2831500000000000000000000000000000 : ℝ)*base79 + (83649217073/11326000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18778819/2500000000000000000000 : ℝ)*base90 + (18778819/2500000000000000000000 : ℝ)*base92 + (18778819/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58529/100000 : ℝ) ≤ (236758864655377021536068084680839/404500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1755743/50000000000000 : ℝ)*(lower1) + (12816501/100000000000000 : ℝ)*(lower2) + (6378579/50000000000000 : ℝ)*(lower5) + (1830913120571703/100000000000000 : ℝ)*(major0) + (1830913120571703/100000000000000 : ℝ)*(major1) + (1830913120571703/100000000000000 : ℝ)*(major2) + (1306557482315431/50000000000000 : ℝ)*(sp0) + (52262079338761/2000000000000 : ℝ)*(sp1) + (1306557292204249/50000000000000 : ℝ)*(sp2) + (102919837907403/10000000000000 : ℝ)*(sp3) + (266894807/10000000000000 : ℝ)*(sp6) + (48868447/25000000000000 : ℝ)*(sp7) + (1144362853/50000000000000 : ℝ)*(sp8) + (6643209259/50000000000000 : ℝ)*(sp9) + (1029198574547819/100000000000000 : ℝ)*(f.failure) + (2613117253356567/100000000000000 : ℝ)*(f.sum) + (2637291933897/809000000000000000000000000 : ℝ)*base65 + (8614295406756202129/809000000000000000000000000000000 : ℝ)*base68 + (6515057169726202129/809000000000000000000000000000000 : ℝ)*base70 + (5720293597384202129/809000000000000000000000000000000 : ℝ)*base72 + (1351358219567/809000000000000000000000000 : ℝ)*base74 + (6230357549642202129/809000000000000000000000000000000 : ℝ)*base76 + (5389175803084202129/809000000000000000000000000000000 : ℝ)*base78 + (6179841861618202129/809000000000000000000000000000000 : ℝ)*base80 + (508553639507/161800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (59199853/5000000000000000000000 : ℝ)*base89 + (59199853/5000000000000000000000 : ℝ)*base91 + (59199853/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (81031/100000 : ℝ) ≤ (81945145922461394942942087363859/101125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24514279/100000000000000 : ℝ)*(lower2) + (18783799/12500000000000 : ℝ)*(lower3) + (9005047/5000000000000 : ℝ)*(upper4) + (964015628451729/50000000000000 : ℝ)*(major0) + (964015628451729/50000000000000 : ℝ)*(major1) + (964015628451729/50000000000000 : ℝ)*(major2) + (6030907331/100000000000000 : ℝ)*(sp1) + (3900983113/12500000000000 : ℝ)*(sp2) + (10833562411/50000000000000 : ℝ)*(sp3) + (31486933/100000000000000 : ℝ)*(sp4) + (1372630193075031/50000000000000 : ℝ)*(sp8) + (42894599792651/1562500000000 : ℝ)*(sp9) + (274522920977209/10000000000000 : ℝ)*(sp10) + (270942314024977/25000000000000 : ℝ)*(sp11) + (108379092322473/10000000000000 : ℝ)*(f.failure) + (1372630208818497/50000000000000 : ℝ)*(f.sum) + (2656137606391/809000000000000000000000000 : ℝ)*base66 + (386460832163587047/404500000000000000000000000000000 : ℝ)*base68 + (1248636887968087047/404500000000000000000000000000000 : ℝ)*base70 + (96888556135087047/404500000000000000000000000000000 : ℝ)*base72 + (59498722219/80900000000000000000000000 : ℝ)*base73 + (2619177792162587047/404500000000000000000000000000000 : ℝ)*base76 + (1876629254412587047/404500000000000000000000000000000 : ℝ)*base78 + (1193603909549412953/404500000000000000000000000000000 : ℝ)*base79 + (82339245107/80900000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (551649/500000000000000000000 : ℝ)*base90 + (551649/500000000000000000000 : ℝ)*base92 + (551649/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-17627/20000 : ℝ) ≤ (-1247743010246659034495257508885607/1415750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1862519/20000000000000 : ℝ)*(lower3) + (8577791/25000000000000 : ℝ)*(lower4) + (9922067/12500000000000 : ℝ)*(upper5) + (985826986971731/50000000000000 : ℝ)*(major0) + (985826986971731/50000000000000 : ℝ)*(major1) + (985826986971731/50000000000000 : ℝ)*(major2) + (105614219/20000000000000 : ℝ)*(sp4) + (8251275223/100000000000000 : ℝ)*(sp5) + (89463589871/100000000000000 : ℝ)*(sp6) + (10730166189/100000000000000 : ℝ)*(sp7) + (716093206858921/25000000000000 : ℝ)*(sp12) + (2864365104231557/100000000000000 : ℝ)*(sp13) + (2864283891916909/100000000000000 : ℝ)*(sp14) + (554150765178981/50000000000000 : ℝ)*(sp15) + (138539032565519/12500000000000 : ℝ)*(f.failure) + (143218667775339/5000000000000 : ℝ)*(f.sum) + (19661766601457/5663000000000000000000000000 : ℝ)*base66 + (8223179582940961869/2831500000000000000000000000000000 : ℝ)*base67 + (23743402128705961869/2831500000000000000000000000000000 : ℝ)*base69 + (12691081566851538131/2831500000000000000000000000000000 : ℝ)*base72 + (2137248773423/707875000000000000000000000 : ℝ)*base74 + (13120319571447461869/2831500000000000000000000000000000 : ℝ)*base75 + (3333132463793038131/2831500000000000000000000000000000 : ℝ)*base78 + (10069458962567461869/2831500000000000000000000000000000 : ℝ)*base79 + (13160361843079/2831500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5919753/625000000000000000000 : ℝ)*base89 + (5919753/625000000000000000000 : ℝ)*base91 + (5919753/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1641_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3257/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65031/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (81031/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17627/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1641_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1641_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65031/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (81031/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17627/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1641_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1641_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1641_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65031/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (81031/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17627/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1641_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
