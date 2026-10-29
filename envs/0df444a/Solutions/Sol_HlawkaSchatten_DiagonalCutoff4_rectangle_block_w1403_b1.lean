-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:46:41.688176+00:00
-- url     : https://prove2.me/submissions/0b4e3fef-8c44-469a-aba6-b8214a9bf838

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
theorem support_rectangle_w1403_s3_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991190093/10000000000 : ℝ)*x 0 + (1084000173/2000000000 : ℝ)*x 1 + (1047333109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991190093/10000000000 : ℝ)^4363 ≤ (12138515058751/100000000000000 : ℝ)^3339 := by
    have hnat : (1991190093 : ℕ)^4363*100000000000000^3339 ≤ 12138515058751^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991190093 10000000000 12138515058751 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084000173/2000000000 : ℝ)^4363 ≤ (22459115196807/50000000000000 : ℝ)^3339 := by
    have hnat : (1084000173 : ℕ)^4363*50000000000000^3339 ≤ 22459115196807^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084000173 2000000000 22459115196807 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047333109/2000000000 : ℝ)^4363 ≤ (5367906816201/12500000000000 : ℝ)^3339 := by
    have hnat : (1047333109 : ℕ)^4363*12500000000000^3339 ≤ 5367906816201^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047333109 2000000000 5367906816201 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991190093/10000000000 : ℝ), (1084000173/2000000000 : ℝ), (1047333109/2000000000 : ℝ)] ![(12138515058751/100000000000000 : ℝ), (22459115196807/50000000000000 : ℝ), (5367906816201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991190093/10000000000 : ℝ)|^4363 ≤ (12138515058751/100000000000000 : ℝ)^3339
        have hw : |(-1991190093/10000000000 : ℝ)|=(1991190093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084000173/2000000000 : ℝ)|^4363 ≤ (22459115196807/50000000000000 : ℝ)^3339
        have hw : |(1084000173/2000000000 : ℝ)|=(1084000173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047333109/2000000000 : ℝ)|^4363 ≤ (5367906816201/12500000000000 : ℝ)^3339
        have hw : |(1047333109/2000000000 : ℝ)|=(1047333109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675273687/5000000000 : ℝ)*x 0 + (-2084757161/10000000000 : ℝ)*x 1 + (2618332753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675273687/5000000000 : ℝ)^4363 ≤ (70668150971/160000000000 : ℝ)^3339 := by
    have hnat : (2675273687 : ℕ)^4363*160000000000^3339 ≤ 70668150971^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675273687 5000000000 70668150971 160000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084757161/10000000000 : ℝ)^4363 ≤ (6444575757167/50000000000000 : ℝ)^3339 := by
    have hnat : (2084757161 : ℕ)^4363*50000000000000^3339 ≤ 6444575757167^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084757161 10000000000 6444575757167 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618332753/5000000000 : ℝ)^4363 ≤ (42943254111707/100000000000000 : ℝ)^3339 := by
    have hnat : (2618332753 : ℕ)^4363*100000000000000^3339 ≤ 42943254111707^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618332753 5000000000 42943254111707 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675273687/5000000000 : ℝ), (-2084757161/10000000000 : ℝ), (2618332753/5000000000 : ℝ)] ![(70668150971/160000000000 : ℝ), (6444575757167/50000000000000 : ℝ), (42943254111707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675273687/5000000000 : ℝ)|^4363 ≤ (70668150971/160000000000 : ℝ)^3339
        have hw : |(2675273687/5000000000 : ℝ)|=(2675273687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084757161/10000000000 : ℝ)|^4363 ≤ (6444575757167/50000000000000 : ℝ)^3339
        have hw : |(-2084757161/10000000000 : ℝ)|=(2084757161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618332753/5000000000 : ℝ)|^4363 ≤ (42943254111707/100000000000000 : ℝ)^3339
        have hw : |(2618332753/5000000000 : ℝ)|=(2618332753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350547393/10000000000 : ℝ)*x 0 + (5236665539/10000000000 : ℝ)*x 1 + (-521189273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350547393/10000000000 : ℝ)^4363 ≤ (5520949320227/12500000000000 : ℝ)^3339 := by
    have hnat : (5350547393 : ℕ)^4363*12500000000000^3339 ≤ 5520949320227^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350547393 10000000000 5520949320227 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236665539/10000000000 : ℝ)^4363 ≤ (8588650893063/20000000000000 : ℝ)^3339 := by
    have hnat : (5236665539 : ℕ)^4363*20000000000000^3339 ≤ 8588650893063^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236665539 10000000000 8588650893063 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521189273/2500000000 : ℝ)^4363 ≤ (3222287739227/25000000000000 : ℝ)^3339 := by
    have hnat : (521189273 : ℕ)^4363*25000000000000^3339 ≤ 3222287739227^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521189273 2500000000 3222287739227 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350547393/10000000000 : ℝ), (5236665539/10000000000 : ℝ), (-521189273/2500000000 : ℝ)] ![(5520949320227/12500000000000 : ℝ), (8588650893063/20000000000000 : ℝ), (3222287739227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350547393/10000000000 : ℝ)|^4363 ≤ (5520949320227/12500000000000 : ℝ)^3339
        have hw : |(5350547393/10000000000 : ℝ)|=(5350547393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236665539/10000000000 : ℝ)|^4363 ≤ (8588650893063/20000000000000 : ℝ)^3339
        have hw : |(5236665539/10000000000 : ℝ)|=(5236665539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521189273/2500000000 : ℝ)|^4363 ≤ (3222287739227/25000000000000 : ℝ)^3339
        have hw : |(-521189273/2500000000 : ℝ)|=(521189273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310167511/10000000000 : ℝ)*x 0 + (4117817061/10000000000 : ℝ)*x 1 + (4510657587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310167511/10000000000 : ℝ)^4363 ≤ (16648354453889/50000000000000 : ℝ)^3339 := by
    have hnat : (4310167511 : ℕ)^4363*50000000000000^3339 ≤ 16648354453889^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310167511 10000000000 16648354453889 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117817061/10000000000 : ℝ)^4363 ≤ (31368493423581/100000000000000 : ℝ)^3339 := by
    have hnat : (4117817061 : ℕ)^4363*100000000000000^3339 ≤ 31368493423581^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117817061 10000000000 31368493423581 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510657587/10000000000 : ℝ)^4363 ≤ (4416849705869/12500000000000 : ℝ)^3339 := by
    have hnat : (4510657587 : ℕ)^4363*12500000000000^3339 ≤ 4416849705869^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510657587 10000000000 4416849705869 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310167511/10000000000 : ℝ), (4117817061/10000000000 : ℝ), (4510657587/10000000000 : ℝ)] ![(16648354453889/50000000000000 : ℝ), (31368493423581/100000000000000 : ℝ), (4416849705869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310167511/10000000000 : ℝ)|^4363 ≤ (16648354453889/50000000000000 : ℝ)^3339
        have hw : |(4310167511/10000000000 : ℝ)|=(4310167511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4117817061/10000000000 : ℝ)|^4363 ≤ (31368493423581/100000000000000 : ℝ)^3339
        have hw : |(4117817061/10000000000 : ℝ)|=(4117817061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510657587/10000000000 : ℝ)|^4363 ≤ (4416849705869/12500000000000 : ℝ)^3339
        have hw : |(4510657587/10000000000 : ℝ)|=(4510657587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4978017/25000000 : ℝ)*x 0 + (5237405829/10000000000 : ℝ)*x 1 + (5419256031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4978017/25000000 : ℝ)^4363 ≤ (3034662035291/25000000000000 : ℝ)^3339 := by
    have hnat : (4978017 : ℕ)^4363*25000000000000^3339 ≤ 3034662035291^3339*25000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978017 25000000 3034662035291 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237405829/10000000000 : ℝ)^4363 ≤ (42951187150299/100000000000000 : ℝ)^3339 := by
    have hnat : (5237405829 : ℕ)^4363*100000000000000^3339 ≤ 42951187150299^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237405829 10000000000 42951187150299 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419256031/10000000000 : ℝ)^4363 ≤ (2245508234353/5000000000000 : ℝ)^3339 := by
    have hnat : (5419256031 : ℕ)^4363*5000000000000^3339 ≤ 2245508234353^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419256031 10000000000 2245508234353 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4978017/25000000 : ℝ), (5237405829/10000000000 : ℝ), (5419256031/10000000000 : ℝ)] ![(3034662035291/25000000000000 : ℝ), (42951187150299/100000000000000 : ℝ), (2245508234353/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4978017/25000000 : ℝ)|^4363 ≤ (3034662035291/25000000000000 : ℝ)^3339
        have hw : |(-4978017/25000000 : ℝ)|=(4978017/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237405829/10000000000 : ℝ)|^4363 ≤ (42951187150299/100000000000000 : ℝ)^3339
        have hw : |(5237405829/10000000000 : ℝ)|=(5237405829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419256031/10000000000 : ℝ)|^4363 ≤ (2245508234353/5000000000000 : ℝ)^3339
        have hw : |(5419256031/10000000000 : ℝ)|=(5419256031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303009793/10000000000 : ℝ)*x 0 + (-1902166083/10000000000 : ℝ)*x 1 + (5419256461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303009793/10000000000 : ℝ)^4363 ≤ (2728471099097/6250000000000 : ℝ)^3339 := by
    have hnat : (5303009793 : ℕ)^4363*6250000000000^3339 ≤ 2728471099097^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303009793 10000000000 2728471099097 6250000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902166083/10000000000 : ℝ)^4363 ≤ (11434293059283/100000000000000 : ℝ)^3339 := by
    have hnat : (1902166083 : ℕ)^4363*100000000000000^3339 ≤ 11434293059283^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902166083 10000000000 11434293059283 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419256461/10000000000 : ℝ)^4363 ≤ (22455084671687/50000000000000 : ℝ)^3339 := by
    have hnat : (5419256461 : ℕ)^4363*50000000000000^3339 ≤ 22455084671687^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419256461 10000000000 22455084671687 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303009793/10000000000 : ℝ), (-1902166083/10000000000 : ℝ), (5419256461/10000000000 : ℝ)] ![(2728471099097/6250000000000 : ℝ), (11434293059283/100000000000000 : ℝ), (22455084671687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303009793/10000000000 : ℝ)|^4363 ≤ (2728471099097/6250000000000 : ℝ)^3339
        have hw : |(5303009793/10000000000 : ℝ)|=(5303009793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902166083/10000000000 : ℝ)|^4363 ≤ (11434293059283/100000000000000 : ℝ)^3339
        have hw : |(-1902166083/10000000000 : ℝ)|=(1902166083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419256461/10000000000 : ℝ)|^4363 ≤ (22455084671687/50000000000000 : ℝ)^3339
        have hw : |(5419256461/10000000000 : ℝ)|=(5419256461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33143817/62500000 : ℝ)*x 0 + (2709627879/5000000000 : ℝ)*x 1 + (-1902165783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33143817/62500000 : ℝ)^4363 ≤ (21827773778583/50000000000000 : ℝ)^3339 := by
    have hnat : (33143817 : ℕ)^4363*50000000000000^3339 ≤ 21827773778583^3339*62500000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33143817 62500000 21827773778583 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709627879/5000000000 : ℝ)^4363 ≤ (22455080865421/50000000000000 : ℝ)^3339 := by
    have hnat : (2709627879 : ℕ)^4363*50000000000000^3339 ≤ 22455080865421^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709627879 5000000000 22455080865421 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902165783/10000000000 : ℝ)^4363 ≤ (11434290702873/100000000000000 : ℝ)^3339 := by
    have hnat : (1902165783 : ℕ)^4363*100000000000000^3339 ≤ 11434290702873^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902165783 10000000000 11434290702873 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33143817/62500000 : ℝ), (2709627879/5000000000 : ℝ), (-1902165783/10000000000 : ℝ)] ![(21827773778583/50000000000000 : ℝ), (22455080865421/50000000000000 : ℝ), (11434290702873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33143817/62500000 : ℝ)|^4363 ≤ (21827773778583/50000000000000 : ℝ)^3339
        have hw : |(33143817/62500000 : ℝ)|=(33143817/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709627879/5000000000 : ℝ)|^4363 ≤ (22455080865421/50000000000000 : ℝ)^3339
        have hw : |(2709627879/5000000000 : ℝ)|=(2709627879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902165783/10000000000 : ℝ)|^4363 ≤ (11434290702873/100000000000000 : ℝ)^3339
        have hw : |(-1902165783/10000000000 : ℝ)|=(1902165783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s3_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310203609/10000000000 : ℝ)*x 0 + (14090847/31250000 : ℝ)*x 1 + (205970589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310203609/10000000000 : ℝ)^4363 ≤ (1331882931683/4000000000000 : ℝ)^3339 := by
    have hnat : (4310203609 : ℕ)^4363*4000000000000^3339 ≤ 1331882931683^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310203609 10000000000 1331882931683 4000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14090847/31250000 : ℝ)^4363 ≤ (17659279290259/50000000000000 : ℝ)^3339 := by
    have hnat : (14090847 : ℕ)^4363*50000000000000^3339 ≤ 17659279290259^3339*31250000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14090847 31250000 17659279290259 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205970589/500000000 : ℝ)^4363 ≤ (627687362351/2000000000000 : ℝ)^3339 := by
    have hnat : (205970589 : ℕ)^4363*2000000000000^3339 ≤ 627687362351^3339*500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205970589 500000000 627687362351 2000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310203609/10000000000 : ℝ), (14090847/31250000 : ℝ), (205970589/500000000 : ℝ)] ![(1331882931683/4000000000000 : ℝ), (17659279290259/50000000000000 : ℝ), (627687362351/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310203609/10000000000 : ℝ)|^4363 ≤ (1331882931683/4000000000000 : ℝ)^3339
        have hw : |(4310203609/10000000000 : ℝ)|=(4310203609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14090847/31250000 : ℝ)|^4363 ≤ (17659279290259/50000000000000 : ℝ)^3339
        have hw : |(14090847/31250000 : ℝ)|=(14090847/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205970589/500000000 : ℝ)|^4363 ≤ (627687362351/2000000000000 : ℝ)^3339
        have hw : |(205970589/500000000 : ℝ)|=(205970589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (277/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7481/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (639/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (639/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (639/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (639/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (639/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (639/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (639/6250 : ℝ) ^ (2181/512 : ℝ) ≤ (3021251689812497/50000000000000000000 : ℝ) := by
    have hpowers : (639/6250 : ℝ)^2181 ≤ (3021251689812497/50000000000000000000 : ℝ)^512 := by
      have hnat : (639 : ℕ)^2181*50000000000000000000^512 ≤ 3021251689812497^512*6250^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        639 6250 3021251689812497 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (639/6250 : ℝ)) (X := (3021251689812497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15883/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (19730127361213957/50000000000000000000 : ℝ) := by
    have hpowers : (15883/100000 : ℝ)^2181 ≤ (19730127361213957/50000000000000000000 : ℝ)^512 := by
      have hnat : (15883 : ℕ)^2181*50000000000000000000^512 ≤ 19730127361213957^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15883 100000 19730127361213957 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15883/100000 : ℝ)) (X := (19730127361213957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003021251689812497/25000000000000000000 : ℝ) ≤ (2000056737619167/2000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25003021251689812497/25000000000000000000 : ℝ)^512 ≤ (2000056737619167/2000000000000000 : ℝ)^2181 := by
      have hnat : (25003021251689812497 : ℕ)^512*2000000000000000^2181 ≤ 2000056737619167^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003021251689812497 25000000000000000000 2000056737619167 2000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056737619167/2000000000000000 : ℝ)) (X := (25003021251689812497/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011375689525513227/25000000000000000000 : ℝ) ≤ (10001068012703557/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25011375689525513227/25000000000000000000 : ℝ)^512 ≤ (10001068012703557/10000000000000000 : ℝ)^2181 := by
      have hnat : (25011375689525513227 : ℕ)^512*10000000000000000^2181 ≤ 10001068012703557^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011375689525513227 25000000000000000000 10001068012703557 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001068012703557/10000000000000000 : ℝ)) (X := (25011375689525513227/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019730127361213957/25000000000000000000 : ℝ) ≤ (10001852337311279/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25019730127361213957/25000000000000000000 : ℝ)^512 ≤ (10001852337311279/10000000000000000 : ℝ)^2181 := by
      have hnat : (25019730127361213957 : ℕ)^512*10000000000000000^2181 ≤ 10001852337311279^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019730127361213957 25000000000000000000 10001852337311279 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001852337311279/10000000000000000 : ℝ)) (X := (25019730127361213957/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3021251689812497/50000000000000000000 : ℝ) ≤ ((56575567521355630809/56590000000000000000 : ℝ)+2*(392162303861/282950000000000 : ℝ)*(639/6250 : ℝ))^(2181/512 : ℝ) := by
    rw [show (56575567521355630809/56590000000000000000 : ℝ)+2*(392162303861/282950000000000 : ℝ)*(639/6250 : ℝ)=(2000056737619167/2000000000000000 : ℝ) by norm_num, show 1+2*(3021251689812497/50000000000000000000 : ℝ)=(25003021251689812497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19730127361213957/50000000000000000000 : ℝ)+(3021251689812497/50000000000000000000 : ℝ) ≤ ((56575567521355630809/56590000000000000000 : ℝ)+(392162303861/282950000000000 : ℝ)*((15883/100000 : ℝ)+(639/6250 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (56575567521355630809/56590000000000000000 : ℝ)+(392162303861/282950000000000 : ℝ)*((15883/100000 : ℝ)+(639/6250 : ℝ))=(10001068012703557/10000000000000000 : ℝ) by norm_num, show 1+(19730127361213957/50000000000000000000 : ℝ)+(3021251689812497/50000000000000000000 : ℝ)=(25011375689525513227/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19730127361213957/50000000000000000000 : ℝ) ≤ ((56575567521355630809/56590000000000000000 : ℝ)+2*(392162303861/282950000000000 : ℝ)*(15883/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (56575567521355630809/56590000000000000000 : ℝ)+2*(392162303861/282950000000000 : ℝ)*(15883/100000 : ℝ)=(10001852337311279/10000000000000000 : ℝ) by norm_num, show 1+2*(19730127361213957/50000000000000000000 : ℝ)=(25019730127361213957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56575567521355630809/56590000000000000000 : ℝ)*(X 1 0+X 2 0)+(392162303861/282950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (639/6250 : ℝ)) (hi := (15883/100000 : ℝ)) (c := (56575567521355630809/56590000000000000000 : ℝ)) (alpha := (392162303861/282950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56575567521355630809/56590000000000000000 : ℝ)*(X 0 1+X 2 1)+(392162303861/282950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (639/6250 : ℝ)) (hi := (15883/100000 : ℝ)) (c := (56575567521355630809/56590000000000000000 : ℝ)) (alpha := (392162303861/282950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56575567521355630809/56590000000000000000 : ℝ)*(X 0 2+X 1 2)+(392162303861/282950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (639/6250 : ℝ)) (hi := (15883/100000 : ℝ)) (c := (56575567521355630809/56590000000000000000 : ℝ)) (alpha := (392162303861/282950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991190093/10000000000 : ℝ)*X 0 0+(1084000173/2000000000 : ℝ)*X 0 1+(1047333109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675273687/5000000000 : ℝ)*X 1 0+(-2084757161/10000000000 : ℝ)*X 1 1+(2618332753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350547393/10000000000 : ℝ)*X 2 0+(5236665539/10000000000 : ℝ)*X 2 1+(-521189273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310167511/10000000000 : ℝ)*X 0 0+(4117817061/10000000000 : ℝ)*X 0 1+(4510657587/10000000000 : ℝ)*X 0 2+(4310167511/10000000000 : ℝ)*X 1 0+(4117817061/10000000000 : ℝ)*X 1 1+(4510657587/10000000000 : ℝ)*X 1 2+(4310167511/10000000000 : ℝ)*X 2 0+(4117817061/10000000000 : ℝ)*X 2 1+(4510657587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4978017/25000000 : ℝ)*X 0 0+(5237405829/10000000000 : ℝ)*X 0 1+(5419256031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303009793/10000000000 : ℝ)*X 1 0+(-1902166083/10000000000 : ℝ)*X 1 1+(5419256461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33143817/62500000 : ℝ)*X 2 0+(2709627879/5000000000 : ℝ)*X 2 1+(-1902165783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310203609/10000000000 : ℝ)*X 0 0+(14090847/31250000 : ℝ)*X 0 1+(205970589/500000000 : ℝ)*X 0 2+(4310203609/10000000000 : ℝ)*X 1 0+(14090847/31250000 : ℝ)*X 1 1+(205970589/500000000 : ℝ)*X 1 2+(4310203609/10000000000 : ℝ)*X 2 0+(14090847/31250000 : ℝ)*X 2 1+(205970589/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9220724683208975009248317303/1414750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1206602127/100000000000000 : ℝ)*(base19) + (1218080607/100000000000000 : ℝ)*(base23) + (422199/10000000000000 : ℝ)*(lower2) + (123420083/100000000000000 : ℝ)*(upper3) + (99709747/50000000000000 : ℝ)*(upper5) + (2000028261319337/50000000000000 : ℝ)*(major0) + (2000028261319337/50000000000000 : ℝ)*(major1) + (2000028261319337/50000000000000 : ℝ)*(major2) + (2727253422219581/50000000000000 : ℝ)*(sp0) + (5454529190663381/100000000000000 : ℝ)*(sp1) + (5454529179184901/100000000000000 : ℝ)*(sp2) + (636393185524961/25000000000000 : ℝ)*(sp3) + (23552826347/100000000000000 : ℝ)*(sp4) + (9688659827/100000000000000 : ℝ)*(sp7) + (318197803844959/12500000000000 : ℝ)*(f.failure) + (1363632599316377/25000000000000 : ℝ)*(f.sum) + (61911754765633/28295000000000000000000000000 : ℝ)*base65 + (10467096888124553633/2829500000000000000000000000000000 : ℝ)*base67 + (26593265734473553633/2829500000000000000000000000000000 : ℝ)*base69 + (51755457804536553633/2829500000000000000000000000000000 : ℝ)*base71 + (99115796534157/28295000000000000000000000000 : ℝ)*base74 + (21017697109973053633/2829500000000000000000000000000000 : ℝ)*base75 + (42183254780166053633/2829500000000000000000000000000000 : ℝ)*base77 + (68490592761367553633/2829500000000000000000000000000000 : ℝ)*base79 + (11583169303351/3536875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1010497/1250000000000000000000 : ℝ)*base89 + (1010497/1250000000000000000000 : ℝ)*base91 + (1010497/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1056592701638269444648633923/176843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2718265877/100000000000000 : ℝ)*(base19) + (250934899/6250000000000 : ℝ)*(base23) + (96672643/20000000000000 : ℝ)*(upper3) + (240893/312500000000 : ℝ)*(lower4) + (578729/200000000000 : ℝ)*(upper5) + (252043166946683/6250000000000 : ℝ)*(major0) + (252043166946683/6250000000000 : ℝ)*(major1) + (252043166946683/6250000000000 : ℝ)*(major2) + (13668023617/25000000000000 : ℝ)*(sp1) + (75876087749/100000000000000 : ℝ)*(sp2) + (5499030777069963/100000000000000 : ℝ)*(sp4) + (2749486693354809/50000000000000 : ℝ)*(sp5) + (549895088602383/10000000000000 : ℝ)*(sp6) + (3207937957583/125000000000 : ℝ)*(sp7) + (3207937957583/125000000000 : ℝ)*(f.failure) + (5499030777069963/100000000000000 : ℝ)*(f.sum) + (4689356404001/1768437500000000000000000000 : ℝ)*base65 + (425671482483055953/353687500000000000000000000000000 : ℝ)*base68 + (6531491453647680953/353687500000000000000000000000000 : ℝ)*base70 + (1565494310093118453/353687500000000000000000000000000 : ℝ)*base72 + (15108109234203/14147500000000000000000000000 : ℝ)*base73 + (5374815145030618453/353687500000000000000000000000000 : ℝ)*base76 + (850348743018680953/353687500000000000000000000000000 : ℝ)*base78 + (3263688462815305953/353687500000000000000000000000000 : ℝ)*base80 + (49056926926287/14147500000000000000000000000 : ℝ)*base82 + (108689/12500000000000000000 : ℝ)*base89 + (108689/12500000000000000000 : ℝ)*base91 + (108689/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1403_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_s4_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398446381/2000000000 : ℝ)*x 0 + (5411219733/10000000000 : ℝ)*x 1 + (163898787/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398446381/2000000000 : ℝ)^4363 ≤ (2429362888421/20000000000000 : ℝ)^3339 := by
    have hnat : (398446381 : ℕ)^4363*20000000000000^3339 ≤ 2429362888421^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398446381 2000000000 2429362888421 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411219733/10000000000 : ℝ)^4363 ≤ (44823162332583/100000000000000 : ℝ)^3339 := by
    have hnat : (5411219733 : ℕ)^4363*100000000000000^3339 ≤ 44823162332583^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411219733 10000000000 44823162332583 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163898787/312500000 : ℝ)^4363 ≤ (107575058003/250000000000 : ℝ)^3339 := by
    have hnat : (163898787 : ℕ)^4363*250000000000^3339 ≤ 107575058003^3339*312500000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163898787 312500000 107575058003 250000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398446381/2000000000 : ℝ), (5411219733/10000000000 : ℝ), (163898787/312500000 : ℝ)] ![(2429362888421/20000000000000 : ℝ), (44823162332583/100000000000000 : ℝ), (107575058003/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398446381/2000000000 : ℝ)|^4363 ≤ (2429362888421/20000000000000 : ℝ)^3339
        have hw : |(-398446381/2000000000 : ℝ)|=(398446381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411219733/10000000000 : ℝ)|^4363 ≤ (44823162332583/100000000000000 : ℝ)^3339
        have hw : |(5411219733/10000000000 : ℝ)|=(5411219733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163898787/312500000 : ℝ)|^4363 ≤ (107575058003/250000000000 : ℝ)^3339
        have hw : |(163898787/312500000 : ℝ)|=(163898787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348289119/10000000000 : ℝ)*x 0 + (-2077027303/10000000000 : ℝ)*x 1 + (524476107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348289119/10000000000 : ℝ)^4363 ≤ (44143237614883/100000000000000 : ℝ)^3339 := by
    have hnat : (5348289119 : ℕ)^4363*100000000000000^3339 ≤ 44143237614883^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348289119 10000000000 44143237614883 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077027303/10000000000 : ℝ)^4363 ≤ (12826740396167/100000000000000 : ℝ)^3339 := by
    have hnat : (2077027303 : ℕ)^4363*100000000000000^3339 ≤ 12826740396167^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077027303 10000000000 12826740396167 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524476107/1000000000 : ℝ)^4363 ≤ (5378752747383/12500000000000 : ℝ)^3339 := by
    have hnat : (524476107 : ℕ)^4363*12500000000000^3339 ≤ 5378752747383^3339*1000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524476107 1000000000 5378752747383 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348289119/10000000000 : ℝ), (-2077027303/10000000000 : ℝ), (524476107/1000000000 : ℝ)] ![(44143237614883/100000000000000 : ℝ), (12826740396167/100000000000000 : ℝ), (5378752747383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348289119/10000000000 : ℝ)|^4363 ≤ (44143237614883/100000000000000 : ℝ)^3339
        have hw : |(5348289119/10000000000 : ℝ)|=(5348289119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077027303/10000000000 : ℝ)|^4363 ≤ (12826740396167/100000000000000 : ℝ)^3339
        have hw : |(-2077027303/10000000000 : ℝ)|=(2077027303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524476107/1000000000 : ℝ)|^4363 ≤ (5378752747383/12500000000000 : ℝ)^3339
        have hw : |(524476107/1000000000 : ℝ)|=(524476107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348289039/10000000000 : ℝ)*x 0 + (1311190281/2500000000 : ℝ)*x 1 + (-2077027337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348289039/10000000000 : ℝ)^4363 ≤ (44143236752087/100000000000000 : ℝ)^3339 := by
    have hnat : (5348289039 : ℕ)^4363*100000000000000^3339 ≤ 44143236752087^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348289039 10000000000 44143236752087 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311190281/2500000000 : ℝ)^4363 ≤ (4303002255797/10000000000000 : ℝ)^3339 := by
    have hnat : (1311190281 : ℕ)^4363*10000000000000^3339 ≤ 4303002255797^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311190281 2500000000 4303002255797 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077027337/10000000000 : ℝ)^4363 ≤ (200417822977/1562500000000 : ℝ)^3339 := by
    have hnat : (2077027337 : ℕ)^4363*1562500000000^3339 ≤ 200417822977^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077027337 10000000000 200417822977 1562500000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348289039/10000000000 : ℝ), (1311190281/2500000000 : ℝ), (-2077027337/10000000000 : ℝ)] ![(44143236752087/100000000000000 : ℝ), (4303002255797/10000000000000 : ℝ), (200417822977/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348289039/10000000000 : ℝ)|^4363 ≤ (44143236752087/100000000000000 : ℝ)^3339
        have hw : |(5348289039/10000000000 : ℝ)|=(5348289039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311190281/2500000000 : ℝ)|^4363 ≤ (4303002255797/10000000000000 : ℝ)^3339
        have hw : |(1311190281/2500000000 : ℝ)|=(1311190281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077027337/10000000000 : ℝ)|^4363 ≤ (200417822977/1562500000000 : ℝ)^3339
        have hw : |(-2077027337/10000000000 : ℝ)|=(2077027337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077701117/2500000000 : ℝ)*x 0 + (4135820723/10000000000 : ℝ)*x 1 + (4492498967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077701117/2500000000 : ℝ)^4363 ≤ (6660627736953/20000000000000 : ℝ)^3339 := by
    have hnat : (1077701117 : ℕ)^4363*20000000000000^3339 ≤ 6660627736953^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077701117 2500000000 6660627736953 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135820723/10000000000 : ℝ)^4363 ≤ (31547820978031/100000000000000 : ℝ)^3339 := by
    have hnat : (4135820723 : ℕ)^4363*100000000000000^3339 ≤ 31547820978031^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135820723 10000000000 31547820978031 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492498967/10000000000 : ℝ)^4363 ≤ (878726007927/2500000000000 : ℝ)^3339 := by
    have hnat : (4492498967 : ℕ)^4363*2500000000000^3339 ≤ 878726007927^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492498967 10000000000 878726007927 2500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077701117/2500000000 : ℝ), (4135820723/10000000000 : ℝ), (4492498967/10000000000 : ℝ)] ![(6660627736953/20000000000000 : ℝ), (31547820978031/100000000000000 : ℝ), (878726007927/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077701117/2500000000 : ℝ)|^4363 ≤ (6660627736953/20000000000000 : ℝ)^3339
        have hw : |(1077701117/2500000000 : ℝ)|=(1077701117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135820723/10000000000 : ℝ)|^4363 ≤ (31547820978031/100000000000000 : ℝ)^3339
        have hw : |(4135820723/10000000000 : ℝ)|=(4135820723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492498967/10000000000 : ℝ)|^4363 ≤ (878726007927/2500000000000 : ℝ)^3339
        have hw : |(4492498967/10000000000 : ℝ)|=(4492498967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199224417/1000000000 : ℝ)*x 0 + (5245371709/10000000000 : ℝ)*x 1 + (2705302991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199224417/1000000000 : ℝ)^4363 ≤ (12146912156661/100000000000000 : ℝ)^3339 := by
    have hnat : (199224417 : ℕ)^4363*100000000000000^3339 ≤ 12146912156661^3339*1000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199224417 1000000000 12146912156661 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245371709/10000000000 : ℝ)^4363 ≤ (4303656844549/10000000000000 : ℝ)^3339 := by
    have hnat : (5245371709 : ℕ)^4363*10000000000000^3339 ≤ 4303656844549^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245371709 10000000000 4303656844549 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705302991/5000000000 : ℝ)^4363 ≤ (22408259692873/50000000000000 : ℝ)^3339 := by
    have hnat : (2705302991 : ℕ)^4363*50000000000000^3339 ≤ 22408259692873^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705302991 5000000000 22408259692873 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199224417/1000000000 : ℝ), (5245371709/10000000000 : ℝ), (2705302991/5000000000 : ℝ)] ![(12146912156661/100000000000000 : ℝ), (4303656844549/10000000000000 : ℝ), (22408259692873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199224417/1000000000 : ℝ)|^4363 ≤ (12146912156661/100000000000000 : ℝ)^3339
        have hw : |(-199224417/1000000000 : ℝ)|=(199224417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245371709/10000000000 : ℝ)|^4363 ≤ (4303656844549/10000000000000 : ℝ)^3339
        have hw : |(5245371709/10000000000 : ℝ)|=(5245371709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705302991/5000000000 : ℝ)|^4363 ≤ (22408259692873/50000000000000 : ℝ)^3339
        have hw : |(2705302991/5000000000 : ℝ)|=(2705302991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305127093/10000000000 : ℝ)*x 0 + (-955591187/5000000000 : ℝ)*x 1 + (5410606107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305127093/10000000000 : ℝ)^4363 ≤ (21839157244699/50000000000000 : ℝ)^3339 := by
    have hnat : (5305127093 : ℕ)^4363*50000000000000^3339 ≤ 21839157244699^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305127093 10000000000 21839157244699 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955591187/5000000000 : ℝ)^4363 ≤ (575258237539/5000000000000 : ℝ)^3339 := by
    have hnat : (955591187 : ℕ)^4363*5000000000000^3339 ≤ 575258237539^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955591187 5000000000 575258237539 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410606107/10000000000 : ℝ)^4363 ≤ (44816520738663/100000000000000 : ℝ)^3339 := by
    have hnat : (5410606107 : ℕ)^4363*100000000000000^3339 ≤ 44816520738663^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410606107 10000000000 44816520738663 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305127093/10000000000 : ℝ), (-955591187/5000000000 : ℝ), (5410606107/10000000000 : ℝ)] ![(21839157244699/50000000000000 : ℝ), (575258237539/5000000000000 : ℝ), (44816520738663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305127093/10000000000 : ℝ)|^4363 ≤ (21839157244699/50000000000000 : ℝ)^3339
        have hw : |(5305127093/10000000000 : ℝ)|=(5305127093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955591187/5000000000 : ℝ)|^4363 ≤ (575258237539/5000000000000 : ℝ)^3339
        have hw : |(-955591187/5000000000 : ℝ)|=(955591187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410606107/10000000000 : ℝ)|^4363 ≤ (44816520738663/100000000000000 : ℝ)^3339
        have hw : |(5410606107/10000000000 : ℝ)|=(5410606107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305127069/10000000000 : ℝ)*x 0 + (5410606041/10000000000 : ℝ)*x 1 + (-1911182499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305127069/10000000000 : ℝ)^4363 ≤ (21839157115601/50000000000000 : ℝ)^3339 := by
    have hnat : (5305127069 : ℕ)^4363*50000000000000^3339 ≤ 21839157115601^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305127069 10000000000 21839157115601 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410606041/10000000000 : ℝ)^4363 ≤ (44816520024323/100000000000000 : ℝ)^3339 := by
    have hnat : (5410606041 : ℕ)^4363*100000000000000^3339 ≤ 44816520024323^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410606041 10000000000 44816520024323 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1911182499/10000000000 : ℝ)^4363 ≤ (5752582867021/50000000000000 : ℝ)^3339 := by
    have hnat : (1911182499 : ℕ)^4363*50000000000000^3339 ≤ 5752582867021^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911182499 10000000000 5752582867021 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305127069/10000000000 : ℝ), (5410606041/10000000000 : ℝ), (-1911182499/10000000000 : ℝ)] ![(21839157115601/50000000000000 : ℝ), (44816520024323/100000000000000 : ℝ), (5752582867021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305127069/10000000000 : ℝ)|^4363 ≤ (21839157115601/50000000000000 : ℝ)^3339
        have hw : |(5305127069/10000000000 : ℝ)|=(5305127069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410606041/10000000000 : ℝ)|^4363 ≤ (44816520024323/100000000000000 : ℝ)^3339
        have hw : |(5410606041/10000000000 : ℝ)|=(5410606041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1911182499/10000000000 : ℝ)|^4363 ≤ (5752582867021/50000000000000 : ℝ)^3339
        have hw : |(-1911182499/10000000000 : ℝ)|=(1911182499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s4_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107770761/250000000 : ℝ)*x 0 + (4491190679/10000000000 : ℝ)*x 1 + (2068568099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107770761/250000000 : ℝ)^4363 ≤ (6660680173179/20000000000000 : ℝ)^3339 := by
    have hnat : (107770761 : ℕ)^4363*20000000000000^3339 ≤ 6660680173179^3339*250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107770761 250000000 6660680173179 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491190679/10000000000 : ℝ)^4363 ≤ (548994778061/1562500000000 : ℝ)^3339 := by
    have hnat : (4491190679 : ℕ)^4363*1562500000000^3339 ≤ 548994778061^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491190679 10000000000 548994778061 1562500000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068568099/5000000000 : ℝ)^4363 ≤ (6312186663807/20000000000000 : ℝ)^3339 := by
    have hnat : (2068568099 : ℕ)^4363*20000000000000^3339 ≤ 6312186663807^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068568099 5000000000 6312186663807 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107770761/250000000 : ℝ), (4491190679/10000000000 : ℝ), (2068568099/5000000000 : ℝ)] ![(6660680173179/20000000000000 : ℝ), (548994778061/1562500000000 : ℝ), (6312186663807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107770761/250000000 : ℝ)|^4363 ≤ (6660680173179/20000000000000 : ℝ)^3339
        have hw : |(107770761/250000000 : ℝ)|=(107770761/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491190679/10000000000 : ℝ)|^4363 ≤ (548994778061/1562500000000 : ℝ)^3339
        have hw : |(4491190679/10000000000 : ℝ)|=(4491190679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068568099/5000000000 : ℝ)|^4363 ≤ (6312186663807/20000000000000 : ℝ)^3339
        have hw : |(2068568099/5000000000 : ℝ)|=(2068568099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7389/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (277/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7481/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (277/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (277/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7481/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (277/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (277/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7481/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (277/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (277/2500 : ℝ) ^ (2181/512 : ℝ) ≤ (2127665364610739/25000000000000000000 : ℝ) := by
    have hpowers : (277/2500 : ℝ)^2181 ≤ (2127665364610739/25000000000000000000 : ℝ)^512 := by
      have hnat : (277 : ℕ)^2181*25000000000000000000^512 ≤ 2127665364610739^512*2500^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        277 2500 2127665364610739 25000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (277/2500 : ℝ)) (X := (2127665364610739/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7481/50000 : ℝ) ^ (2181/512 : ℝ) ≤ (30594916519948487/100000000000000000000 : ℝ) := by
    have hpowers : (7481/50000 : ℝ)^2181 ≤ (30594916519948487/100000000000000000000 : ℝ)^512 := by
      have hnat : (7481 : ℕ)^2181*100000000000000000000^512 ≤ 30594916519948487^512*50000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7481 50000 30594916519948487 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7481/50000 : ℝ)) (X := (30594916519948487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502127665364610739/12500000000000000000 : ℝ) ≤ (10000399557533703/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (12502127665364610739/12500000000000000000 : ℝ)^512 ≤ (10000399557533703/10000000000000000 : ℝ)^2181 := by
      have hnat : (12502127665364610739 : ℕ)^512*10000000000000000^2181 ≤ 10000399557533703^2181*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502127665364610739 12500000000000000000 10000399557533703 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399557533703/10000000000000000 : ℝ)) (X := (12502127665364610739/12500000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039105577978391443/100000000000000000000 : ℝ) ≤ (5000458942246171/5000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (100039105577978391443/100000000000000000000 : ℝ)^512 ≤ (5000458942246171/5000000000000000 : ℝ)^2181 := by
      have hnat : (100039105577978391443 : ℕ)^512*5000000000000000^2181 ≤ 5000458942246171^2181*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039105577978391443 100000000000000000000 5000458942246171 5000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000458942246171/5000000000000000 : ℝ)) (X := (100039105577978391443/100000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030594916519948487/50000000000000000000 : ℝ) ≤ (10001436211450981/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50030594916519948487/50000000000000000000 : ℝ)^512 ≤ (10001436211450981/10000000000000000 : ℝ)^2181 := by
      have hnat : (50030594916519948487 : ℕ)^512*10000000000000000^2181 ≤ 10001436211450981^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030594916519948487 50000000000000000000 10001436211450981 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001436211450981/10000000000000000 : ℝ)) (X := (50030594916519948487/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2127665364610739/25000000000000000000 : ℝ) ≤ ((19405032478471197403/19410000000000000000 : ℝ)+2*(518326958639/388200000000000 : ℝ)*(277/2500 : ℝ))^(2181/512 : ℝ) := by
    rw [show (19405032478471197403/19410000000000000000 : ℝ)+2*(518326958639/388200000000000 : ℝ)*(277/2500 : ℝ)=(10000399557533703/10000000000000000 : ℝ) by norm_num, show 1+2*(2127665364610739/25000000000000000000 : ℝ)=(12502127665364610739/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30594916519948487/100000000000000000000 : ℝ)+(2127665364610739/25000000000000000000 : ℝ) ≤ ((19405032478471197403/19410000000000000000 : ℝ)+(518326958639/388200000000000 : ℝ)*((7481/50000 : ℝ)+(277/2500 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (19405032478471197403/19410000000000000000 : ℝ)+(518326958639/388200000000000 : ℝ)*((7481/50000 : ℝ)+(277/2500 : ℝ))=(5000458942246171/5000000000000000 : ℝ) by norm_num, show 1+(30594916519948487/100000000000000000000 : ℝ)+(2127665364610739/25000000000000000000 : ℝ)=(100039105577978391443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30594916519948487/100000000000000000000 : ℝ) ≤ ((19405032478471197403/19410000000000000000 : ℝ)+2*(518326958639/388200000000000 : ℝ)*(7481/50000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (19405032478471197403/19410000000000000000 : ℝ)+2*(518326958639/388200000000000 : ℝ)*(7481/50000 : ℝ)=(10001436211450981/10000000000000000 : ℝ) by norm_num, show 1+2*(30594916519948487/100000000000000000000 : ℝ)=(50030594916519948487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19405032478471197403/19410000000000000000 : ℝ)*(X 1 0+X 2 0)+(518326958639/388200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (19405032478471197403/19410000000000000000 : ℝ)) (alpha := (518326958639/388200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19405032478471197403/19410000000000000000 : ℝ)*(X 0 1+X 2 1)+(518326958639/388200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (19405032478471197403/19410000000000000000 : ℝ)) (alpha := (518326958639/388200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19405032478471197403/19410000000000000000 : ℝ)*(X 0 2+X 1 2)+(518326958639/388200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (7481/50000 : ℝ)) (c := (19405032478471197403/19410000000000000000 : ℝ)) (alpha := (518326958639/388200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398446381/2000000000 : ℝ)*X 0 0+(5411219733/10000000000 : ℝ)*X 0 1+(163898787/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348289119/10000000000 : ℝ)*X 1 0+(-2077027303/10000000000 : ℝ)*X 1 1+(524476107/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348289039/10000000000 : ℝ)*X 2 0+(1311190281/2500000000 : ℝ)*X 2 1+(-2077027337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077701117/2500000000 : ℝ)*X 0 0+(4135820723/10000000000 : ℝ)*X 0 1+(4492498967/10000000000 : ℝ)*X 0 2+(1077701117/2500000000 : ℝ)*X 1 0+(4135820723/10000000000 : ℝ)*X 1 1+(4492498967/10000000000 : ℝ)*X 1 2+(1077701117/2500000000 : ℝ)*X 2 0+(4135820723/10000000000 : ℝ)*X 2 1+(4492498967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-199224417/1000000000 : ℝ)*X 0 0+(5245371709/10000000000 : ℝ)*X 0 1+(2705302991/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305127093/10000000000 : ℝ)*X 1 0+(-955591187/5000000000 : ℝ)*X 1 1+(5410606107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305127069/10000000000 : ℝ)*X 2 0+(5410606041/10000000000 : ℝ)*X 2 1+(-1911182499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107770761/250000000 : ℝ)*X 0 0+(4491190679/10000000000 : ℝ)*X 0 1+(2068568099/5000000000 : ℝ)*X 0 2+(107770761/250000000 : ℝ)*X 1 0+(4491190679/10000000000 : ℝ)*X 1 1+(2068568099/5000000000 : ℝ)*X 1 2+(107770761/250000000 : ℝ)*X 2 0+(4491190679/10000000000 : ℝ)*X 2 1+(2068568099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152648135515992208917901149/32350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146545109/12500000000000 : ℝ)*(base19) + (980252717/100000000000000 : ℝ)*(base23) + (27342349/50000000000000 : ℝ)*(lower2) + (55440797/25000000000000 : ℝ)*(upper3) + (88670609/100000000000000 : ℝ)*(upper5) + (440560234481017/10000000000000 : ℝ)*(major0) + (440560234481017/10000000000000 : ℝ)*(major1) + (440560234481017/10000000000000 : ℝ)*(major2) + (750940256859129/12500000000000 : ℝ)*(sp0) + (3003768498080469/50000000000000 : ℝ)*(sp1) + (3003768594134547/50000000000000 : ℝ)*(sp2) + (2803655778872991/100000000000000 : ℝ)*(sp3) + (8056824389/50000000000000 : ℝ)*(sp4) + (5292468697/50000000000000 : ℝ)*(sp7) + (175229147738149/6250000000000 : ℝ)*(f.failure) + (600753816852181/10000000000000 : ℝ)*(f.sum) + (1193963434277/388200000000000000000000000 : ℝ)*base66 + (21131339610648851/194100000000000000000000000000000 : ℝ)*base67 + (1085039418795048851/194100000000000000000000000000000 : ℝ)*base69 + (566372662599348851/194100000000000000000000000000000 : ℝ)*base71 + (507080580679/970500000000000000000000000 : ℝ)*base73 + (948916355873448851/194100000000000000000000000000000 : ℝ)*base75 + (470980626641051149/194100000000000000000000000000000 : ℝ)*base78 + (873735576361151149/194100000000000000000000000000000 : ℝ)*base80 + (2322348916523/485250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7005733/625000000000000000000 : ℝ)*base90 + (7005733/625000000000000000000 : ℝ)*base92 + (7005733/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9262711358859388577295009/1263671875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1202583587/100000000000000 : ℝ)*(base19) + (578440329/50000000000000 : ℝ)*(base23) + (15012859/100000000000000 : ℝ)*(upper2) + (72246989/50000000000000 : ℝ)*(upper3) + (194501399/100000000000000 : ℝ)*(upper5) + (4334197930443/97656250000 : ℝ)*(major0) + (4334197930443/97656250000 : ℝ)*(major1) + (4334197930443/97656250000 : ℝ)*(major2) + (14563871959/50000000000000 : ℝ)*(sp1) + (23397271249/100000000000000 : ℝ)*(sp2) + (6052014153761989/100000000000000 : ℝ)*(sp4) + (6051983823434483/100000000000000 : ℝ)*(sp5) + (6051989599610081/100000000000000 : ℝ)*(sp6) + (1412211481726013/50000000000000 : ℝ)*(sp7) + (1412211481726013/50000000000000 : ℝ)*(f.failure) + (6052014153761989/100000000000000 : ℝ)*(f.sum) + (5458305515021/1617500000000000000000000000 : ℝ)*base66 + (7790566428211863/10109375000000000000000000000000 : ℝ)*base67 + (45485073486495631/5054687500000000000000000000000 : ℝ)*base70 + (83040581324118113/10109375000000000000000000000000 : ℝ)*base71 + (1084023511411/1617500000000000000000000000 : ℝ)*base74 + (50538440406368113/10109375000000000000000000000000 : ℝ)*base75 + (9732469737541247/2527343750000000000000000000000 : ℝ)*base77 + (62176963812600637/10109375000000000000000000000000 : ℝ)*base80 + (341678956593/50546875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (60641379/5000000000000000000000 : ℝ)*base89 + (60641379/5000000000000000000000 : ℝ)*base91 + (60641379/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1403_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7481/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_s5_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199239497/1000000000 : ℝ)*x 0 + (676223431/1250000000 : ℝ)*x 1 + (5246085967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199239497/1000000000 : ℝ)^4363 ≤ (1518514198343/12500000000000 : ℝ)^3339 := by
    have hnat : (199239497 : ℕ)^4363*12500000000000^3339 ≤ 1518514198343^3339*1000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199239497 1000000000 1518514198343 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676223431/1250000000 : ℝ)^4363 ≤ (1792306413017/4000000000000 : ℝ)^3339 := by
    have hnat : (676223431 : ℕ)^4363*4000000000000^3339 ≤ 1792306413017^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676223431 1250000000 1792306413017 4000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246085967/10000000000 : ℝ)^4363 ≤ (21522113037413/50000000000000 : ℝ)^3339 := by
    have hnat : (5246085967 : ℕ)^4363*50000000000000^3339 ≤ 21522113037413^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246085967 10000000000 21522113037413 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199239497/1000000000 : ℝ), (676223431/1250000000 : ℝ), (5246085967/10000000000 : ℝ)] ![(1518514198343/12500000000000 : ℝ), (1792306413017/4000000000000 : ℝ), (21522113037413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199239497/1000000000 : ℝ)|^4363 ≤ (1518514198343/12500000000000 : ℝ)^3339
        have hw : |(-199239497/1000000000 : ℝ)|=(199239497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676223431/1250000000 : ℝ)|^4363 ≤ (1792306413017/4000000000000 : ℝ)^3339
        have hw : |(676223431/1250000000 : ℝ)|=(676223431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246085967/10000000000 : ℝ)|^4363 ≤ (21522113037413/50000000000000 : ℝ)^3339
        have hw : |(5246085967/10000000000 : ℝ)|=(5246085967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347919849/10000000000 : ℝ)*x 0 + (-16606083/80000000 : ℝ)*x 1 + (2623043023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347919849/10000000000 : ℝ)^4363 ≤ (44139255098891/100000000000000 : ℝ)^3339 := by
    have hnat : (5347919849 : ℕ)^4363*100000000000000^3339 ≤ 44139255098891^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347919849 10000000000 44139255098891 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16606083/80000000 : ℝ)^4363 ≤ (1281651796489/10000000000000 : ℝ)^3339 := by
    have hnat : (16606083 : ℕ)^4363*10000000000000^3339 ≤ 1281651796489^3339*80000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16606083 80000000 1281651796489 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623043023/5000000000 : ℝ)^4363 ≤ (4304422692181/10000000000000 : ℝ)^3339 := by
    have hnat : (2623043023 : ℕ)^4363*10000000000000^3339 ≤ 4304422692181^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623043023 5000000000 4304422692181 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347919849/10000000000 : ℝ), (-16606083/80000000 : ℝ), (2623043023/5000000000 : ℝ)] ![(44139255098891/100000000000000 : ℝ), (1281651796489/10000000000000 : ℝ), (4304422692181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347919849/10000000000 : ℝ)|^4363 ≤ (44139255098891/100000000000000 : ℝ)^3339
        have hw : |(5347919849/10000000000 : ℝ)|=(5347919849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16606083/80000000 : ℝ)|^4363 ≤ (1281651796489/10000000000000 : ℝ)^3339
        have hw : |(-16606083/80000000 : ℝ)|=(16606083/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623043023/5000000000 : ℝ)|^4363 ≤ (4304422692181/10000000000000 : ℝ)^3339
        have hw : |(2623043023/5000000000 : ℝ)|=(2623043023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336979971/2500000000 : ℝ)*x 0 + (5246085841/10000000000 : ℝ)*x 1 + (-10378803/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336979971/2500000000 : ℝ)^4363 ≤ (11034813869089/25000000000000 : ℝ)^3339 := by
    have hnat : (1336979971 : ℕ)^4363*25000000000000^3339 ≤ 11034813869089^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336979971 2500000000 11034813869089 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246085841/10000000000 : ℝ)^4363 ≤ (2152211236197/5000000000000 : ℝ)^3339 := by
    have hnat : (5246085841 : ℕ)^4363*5000000000000^3339 ≤ 2152211236197^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246085841 10000000000 2152211236197 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10378803/50000000 : ℝ)^4363 ≤ (3204129945043/25000000000000 : ℝ)^3339 := by
    have hnat : (10378803 : ℕ)^4363*25000000000000^3339 ≤ 3204129945043^3339*50000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10378803 50000000 3204129945043 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336979971/2500000000 : ℝ), (5246085841/10000000000 : ℝ), (-10378803/50000000 : ℝ)] ![(11034813869089/25000000000000 : ℝ), (2152211236197/5000000000000 : ℝ), (3204129945043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336979971/2500000000 : ℝ)|^4363 ≤ (11034813869089/25000000000000 : ℝ)^3339
        have hw : |(1336979971/2500000000 : ℝ)|=(1336979971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246085841/10000000000 : ℝ)|^4363 ≤ (2152211236197/5000000000000 : ℝ)^3339
        have hw : |(5246085841/10000000000 : ℝ)|=(5246085841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10378803/50000000 : ℝ)|^4363 ≤ (3204129945043/25000000000000 : ℝ)^3339
        have hw : |(-10378803/50000000 : ℝ)|=(10378803/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310901827/10000000000 : ℝ)*x 0 + (4138764147/10000000000 : ℝ)*x 1 + (4489532529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310901827/10000000000 : ℝ)^4363 ≤ (33304121503087/100000000000000 : ℝ)^3339 := by
    have hnat : (4310901827 : ℕ)^4363*100000000000000^3339 ≤ 33304121503087^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310901827 10000000000 33304121503087 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138764147/10000000000 : ℝ)^4363 ≤ (31577162096681/100000000000000 : ℝ)^3339 := by
    have hnat : (4138764147 : ℕ)^4363*100000000000000^3339 ≤ 31577162096681^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138764147 10000000000 31577162096681 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489532529/10000000000 : ℝ)^4363 ≤ (8779679095227/25000000000000 : ℝ)^3339 := by
    have hnat : (4489532529 : ℕ)^4363*25000000000000^3339 ≤ 8779679095227^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489532529 10000000000 8779679095227 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310901827/10000000000 : ℝ), (4138764147/10000000000 : ℝ), (4489532529/10000000000 : ℝ)] ![(33304121503087/100000000000000 : ℝ), (31577162096681/100000000000000 : ℝ), (8779679095227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310901827/10000000000 : ℝ)|^4363 ≤ (33304121503087/100000000000000 : ℝ)^3339
        have hw : |(4310901827/10000000000 : ℝ)|=(4310901827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138764147/10000000000 : ℝ)|^4363 ≤ (31577162096681/100000000000000 : ℝ)^3339
        have hw : |(4138764147/10000000000 : ℝ)|=(4138764147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489532529/10000000000 : ℝ)|^4363 ≤ (8779679095227/25000000000000 : ℝ)^3339
        have hw : |(4489532529/10000000000 : ℝ)|=(4489532529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24905089/125000000 : ℝ)*x 0 + (20494831/39062500 : ℝ)*x 1 + (676149157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24905089/125000000 : ℝ)^4363 ≤ (1214821038753/10000000000000 : ℝ)^3339 := by
    have hnat : (24905089 : ℕ)^4363*10000000000000^3339 ≤ 1214821038753^3339*125000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24905089 125000000 1214821038753 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20494831/39062500 : ℝ)^4363 ≤ (21525280004107/50000000000000 : ℝ)^3339 := by
    have hnat : (20494831 : ℕ)^4363*50000000000000^3339 ≤ 21525280004107^3339*39062500^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20494831 39062500 21525280004107 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676149157/1250000000 : ℝ)^4363 ≤ (44801229594399/100000000000000 : ℝ)^3339 := by
    have hnat : (676149157 : ℕ)^4363*100000000000000^3339 ≤ 44801229594399^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676149157 1250000000 44801229594399 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24905089/125000000 : ℝ), (20494831/39062500 : ℝ), (676149157/1250000000 : ℝ)] ![(1214821038753/10000000000000 : ℝ), (21525280004107/50000000000000 : ℝ), (44801229594399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24905089/125000000 : ℝ)|^4363 ≤ (1214821038753/10000000000000 : ℝ)^3339
        have hw : |(-24905089/125000000 : ℝ)|=(24905089/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20494831/39062500 : ℝ)|^4363 ≤ (21525280004107/50000000000000 : ℝ)^3339
        have hw : |(20494831/39062500 : ℝ)|=(20494831/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676149157/1250000000 : ℝ)|^4363 ≤ (44801229594399/100000000000000 : ℝ)^3339
        have hw : |(676149157/1250000000 : ℝ)|=(676149157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652736363/5000000000 : ℝ)*x 0 + (-382530683/2000000000 : ℝ)*x 1 + (5409193257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652736363/5000000000 : ℝ)^4363 ≤ (43682032909137/100000000000000 : ℝ)^3339 := by
    have hnat : (2652736363 : ℕ)^4363*100000000000000^3339 ≤ 43682032909137^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652736363 5000000000 43682032909137 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382530683/2000000000 : ℝ)^4363 ≤ (2879184368241/25000000000000 : ℝ)^3339 := by
    have hnat : (382530683 : ℕ)^4363*25000000000000^3339 ≤ 2879184368241^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382530683 2000000000 2879184368241 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409193257/10000000000 : ℝ)^4363 ≤ (44801229605221/100000000000000 : ℝ)^3339 := by
    have hnat : (5409193257 : ℕ)^4363*100000000000000^3339 ≤ 44801229605221^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409193257 10000000000 44801229605221 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652736363/5000000000 : ℝ), (-382530683/2000000000 : ℝ), (5409193257/10000000000 : ℝ)] ![(43682032909137/100000000000000 : ℝ), (2879184368241/25000000000000 : ℝ), (44801229605221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652736363/5000000000 : ℝ)|^4363 ≤ (43682032909137/100000000000000 : ℝ)^3339
        have hw : |(2652736363/5000000000 : ℝ)|=(2652736363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382530683/2000000000 : ℝ)|^4363 ≤ (2879184368241/25000000000000 : ℝ)^3339
        have hw : |(-382530683/2000000000 : ℝ)|=(382530683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409193257/10000000000 : ℝ)|^4363 ≤ (44801229605221/100000000000000 : ℝ)^3339
        have hw : |(5409193257/10000000000 : ℝ)|=(5409193257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326368181/2500000000 : ℝ)*x 0 + (2704596629/5000000000 : ℝ)*x 1 + (-382530683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326368181/2500000000 : ℝ)^4363 ≤ (2184101644381/5000000000000 : ℝ)^3339 := by
    have hnat : (1326368181 : ℕ)^4363*5000000000000^3339 ≤ 2184101644381^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326368181 2500000000 2184101644381 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704596629/5000000000 : ℝ)^4363 ≤ (11200307404011/25000000000000 : ℝ)^3339 := by
    have hnat : (2704596629 : ℕ)^4363*25000000000000^3339 ≤ 11200307404011^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704596629 5000000000 11200307404011 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382530683/2000000000 : ℝ)^4363 ≤ (2879184368241/25000000000000 : ℝ)^3339 := by
    have hnat : (382530683 : ℕ)^4363*25000000000000^3339 ≤ 2879184368241^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382530683 2000000000 2879184368241 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326368181/2500000000 : ℝ), (2704596629/5000000000 : ℝ), (-382530683/2000000000 : ℝ)] ![(2184101644381/5000000000000 : ℝ), (11200307404011/25000000000000 : ℝ), (2879184368241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326368181/2500000000 : ℝ)|^4363 ≤ (2184101644381/5000000000000 : ℝ)^3339
        have hw : |(1326368181/2500000000 : ℝ)|=(1326368181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704596629/5000000000 : ℝ)|^4363 ≤ (11200307404011/25000000000000 : ℝ)^3339
        have hw : |(2704596629/5000000000 : ℝ)|=(2704596629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382530683/2000000000 : ℝ)|^4363 ≤ (2879184368241/25000000000000 : ℝ)^3339
        have hw : |(-382530683/2000000000 : ℝ)|=(382530683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s5_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310927423/10000000000 : ℝ)*x 0 + (1122066733/2500000000 : ℝ)*x 1 + (4140035683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310927423/10000000000 : ℝ)^4363 ≤ (33304379890373/100000000000000 : ℝ)^3339 := by
    have hnat : (4310927423 : ℕ)^4363*100000000000000^3339 ≤ 33304379890373^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310927423 10000000000 33304379890373 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122066733/2500000000 : ℝ)^4363 ≤ (274263913191/781250000000 : ℝ)^3339 := by
    have hnat : (1122066733 : ℕ)^4363*781250000000^3339 ≤ 274263913191^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122066733 2500000000 274263913191 781250000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140035683/10000000000 : ℝ)^4363 ≤ (3158983920877/10000000000000 : ℝ)^3339 := by
    have hnat : (4140035683 : ℕ)^4363*10000000000000^3339 ≤ 3158983920877^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140035683 10000000000 3158983920877 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310927423/10000000000 : ℝ), (1122066733/2500000000 : ℝ), (4140035683/10000000000 : ℝ)] ![(33304379890373/100000000000000 : ℝ), (274263913191/781250000000 : ℝ), (3158983920877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310927423/10000000000 : ℝ)|^4363 ≤ (33304379890373/100000000000000 : ℝ)^3339
        have hw : |(4310927423/10000000000 : ℝ)|=(4310927423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122066733/2500000000 : ℝ)|^4363 ≤ (274263913191/781250000000 : ℝ)^3339
        have hw : |(1122066733/2500000000 : ℝ)|=(1122066733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140035683/10000000000 : ℝ)|^4363 ≤ (3158983920877/10000000000000 : ℝ)^3339
        have hw : |(4140035683/10000000000 : ℝ)|=(4140035683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (4545643806543893/50000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^2181 ≤ (4545643806543893/50000000000000000000 : ℝ)^512 := by
      have hnat : (11253 : ℕ)^2181*50000000000000000000^512 ≤ 4545643806543893^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 4545643806543893 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (4545643806543893/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7389/50000 : ℝ) ^ (2181/512 : ℝ) ≤ (29024005147135559/100000000000000000000 : ℝ) := by
    have hpowers : (7389/50000 : ℝ)^2181 ≤ (29024005147135559/100000000000000000000 : ℝ)^512 := by
      have hnat : (7389 : ℕ)^2181*100000000000000000000^512 ≤ 29024005147135559^512*50000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7389 50000 29024005147135559 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7389/50000 : ℝ)) (X := (29024005147135559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004545643806543893/25000000000000000000 : ℝ) ≤ (10000426814805989/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25004545643806543893/25000000000000000000 : ℝ)^512 ≤ (10000426814805989/10000000000000000 : ℝ)^2181 := by
      have hnat : (25004545643806543893 : ℕ)^512*10000000000000000^2181 ≤ 10000426814805989^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004545643806543893 25000000000000000000 10000426814805989 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000426814805989/10000000000000000 : ℝ)) (X := (25004545643806543893/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007623058552044669/20000000000000000000 : ℝ) ≤ (10000894643947889/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (20007623058552044669/20000000000000000000 : ℝ)^512 ≤ (10000894643947889/10000000000000000 : ℝ)^2181 := by
      have hnat : (20007623058552044669 : ℕ)^512*10000000000000000^2181 ≤ 10000894643947889^2181*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007623058552044669 20000000000000000000 10000894643947889 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000894643947889/10000000000000000 : ℝ)) (X := (20007623058552044669/20000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029024005147135559/50000000000000000000 : ℝ) ≤ (10001362473089789/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50029024005147135559/50000000000000000000 : ℝ)^512 ≤ (10001362473089789/10000000000000000 : ℝ)^2181 := by
      have hnat : (50029024005147135559 : ℕ)^512*10000000000000000^2181 ≤ 10001362473089789^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029024005147135559 50000000000000000000 10001362473089789 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001362473089789/10000000000000000 : ℝ)) (X := (50029024005147135559/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4545643806543893/50000000000000000000 : ℝ) ≤ ((469879674126980131/470000000000000000 : ℝ)+2*(1559430473/1175000000000 : ℝ)*(11253/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (469879674126980131/470000000000000000 : ℝ)+2*(1559430473/1175000000000 : ℝ)*(11253/100000 : ℝ)=(10000426814805989/10000000000000000 : ℝ) by norm_num, show 1+2*(4545643806543893/50000000000000000000 : ℝ)=(25004545643806543893/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29024005147135559/100000000000000000000 : ℝ)+(4545643806543893/50000000000000000000 : ℝ) ≤ ((469879674126980131/470000000000000000 : ℝ)+(1559430473/1175000000000 : ℝ)*((7389/50000 : ℝ)+(11253/100000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (469879674126980131/470000000000000000 : ℝ)+(1559430473/1175000000000 : ℝ)*((7389/50000 : ℝ)+(11253/100000 : ℝ))=(10000894643947889/10000000000000000 : ℝ) by norm_num, show 1+(29024005147135559/100000000000000000000 : ℝ)+(4545643806543893/50000000000000000000 : ℝ)=(20007623058552044669/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29024005147135559/100000000000000000000 : ℝ) ≤ ((469879674126980131/470000000000000000 : ℝ)+2*(1559430473/1175000000000 : ℝ)*(7389/50000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (469879674126980131/470000000000000000 : ℝ)+2*(1559430473/1175000000000 : ℝ)*(7389/50000 : ℝ)=(10001362473089789/10000000000000000 : ℝ) by norm_num, show 1+2*(29024005147135559/100000000000000000000 : ℝ)=(50029024005147135559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (469879674126980131/470000000000000000 : ℝ)*(X 1 0+X 2 0)+(1559430473/1175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (469879674126980131/470000000000000000 : ℝ)) (alpha := (1559430473/1175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (469879674126980131/470000000000000000 : ℝ)*(X 0 1+X 2 1)+(1559430473/1175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (469879674126980131/470000000000000000 : ℝ)) (alpha := (1559430473/1175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (469879674126980131/470000000000000000 : ℝ)*(X 0 2+X 1 2)+(1559430473/1175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (469879674126980131/470000000000000000 : ℝ)) (alpha := (1559430473/1175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-199239497/1000000000 : ℝ)*X 0 0+(676223431/1250000000 : ℝ)*X 0 1+(5246085967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347919849/10000000000 : ℝ)*X 1 0+(-16606083/80000000 : ℝ)*X 1 1+(2623043023/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336979971/2500000000 : ℝ)*X 2 0+(5246085841/10000000000 : ℝ)*X 2 1+(-10378803/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310901827/10000000000 : ℝ)*X 0 0+(4138764147/10000000000 : ℝ)*X 0 1+(4489532529/10000000000 : ℝ)*X 0 2+(4310901827/10000000000 : ℝ)*X 1 0+(4138764147/10000000000 : ℝ)*X 1 1+(4489532529/10000000000 : ℝ)*X 1 2+(4310901827/10000000000 : ℝ)*X 2 0+(4138764147/10000000000 : ℝ)*X 2 1+(4489532529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24905089/125000000 : ℝ)*X 0 0+(20494831/39062500 : ℝ)*X 0 1+(676149157/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652736363/5000000000 : ℝ)*X 1 0+(-382530683/2000000000 : ℝ)*X 1 1+(5409193257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326368181/2500000000 : ℝ)*X 2 0+(2704596629/5000000000 : ℝ)*X 2 1+(-382530683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310927423/10000000000 : ℝ)*X 0 0+(1122066733/2500000000 : ℝ)*X 0 1+(4140035683/10000000000 : ℝ)*X 0 2+(4310927423/10000000000 : ℝ)*X 1 0+(1122066733/2500000000 : ℝ)*X 1 1+(4140035683/10000000000 : ℝ)*X 1 2+(4310927423/10000000000 : ℝ)*X 2 0+(1122066733/2500000000 : ℝ)*X 2 1+(4140035683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107830399403295672856569507/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200467239/20000000000000 : ℝ)*(base19) + (1274002179/100000000000000 : ℝ)*(base23) + (30194861/100000000000000 : ℝ)*(lower2) + (154099029/100000000000000 : ℝ)*(lower4) + (102628989/100000000000000 : ℝ)*(lower5) + (4479826335844299/100000000000000 : ℝ)*(major0) + (4479826335844299/100000000000000 : ℝ)*(major1) + (4479826335844299/100000000000000 : ℝ)*(major2) + (1221743734960589/20000000000000 : ℝ)*(sp0) + (244349993808989/4000000000000 : ℝ)*(sp1) + (6108749573558741/100000000000000 : ℝ)*(sp2) + (1425446232269227/50000000000000 : ℝ)*(sp3) + (4021594747/12500000000000 : ℝ)*(sp4) + (72429499/800000000000 : ℝ)*(sp7) + (2850901518225829/100000000000000 : ℝ)*(f.failure) + (6108750847560921/100000000000000 : ℝ)*(f.sum) + (120160080153/235000000000000000000000000 : ℝ)*base65 + (139954473444576831/47000000000000000000000000000000 : ℝ)*base68 + (158227228760576831/47000000000000000000000000000000 : ℝ)*base70 + (129917943877423169/47000000000000000000000000000000 : ℝ)*base71 + (206462408403/235000000000000000000000000 : ℝ)*base73 + (280544948673576831/47000000000000000000000000000000 : ℝ)*base76 + (196395513515576831/47000000000000000000000000000000 : ℝ)*base78 + (505135331239576831/47000000000000000000000000000000 : ℝ)*base80 + (735052713677/235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26899707/10000000000000000000000 : ℝ)*base89 + (26899707/10000000000000000000000 : ℝ)*base91 + (26899707/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10033264529067576487011039/1468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1170822829/100000000000000 : ℝ)*(base19) + (1265040527/100000000000000 : ℝ)*(base23) + (140625799/100000000000000 : ℝ)*(upper3) + (5469181/12500000000000 : ℝ)*(lower4) + (140158963/100000000000000 : ℝ)*(upper5) + (564054659913477/12500000000000 : ℝ)*(major0) + (564054659913477/12500000000000 : ℝ)*(major1) + (564054659913477/12500000000000 : ℝ)*(major2) + (24369962323/100000000000000 : ℝ)*(sp1) + (6532098769/25000000000000 : ℝ)*(sp2) + (1538304911189411/25000000000000 : ℝ)*(sp4) + (6153194103972491/100000000000000 : ℝ)*(sp5) + (3076596125661021/50000000000000 : ℝ)*(sp6) + (1435827343076341/50000000000000 : ℝ)*(sp7) + (1435827343076341/50000000000000 : ℝ)*(f.failure) + (1538304911189411/25000000000000 : ℝ)*(f.sum) + (123529102231/117500000000000000000000000 : ℝ)*base65 + (62374266159525487/5875000000000000000000000000000 : ℝ)*base67 + (48486241670275487/5875000000000000000000000000000 : ℝ)*base69 + (58185705054900487/5875000000000000000000000000000 : ℝ)*base71 + (593366890191/117500000000000000000000000 : ℝ)*base73 + (190734742731900487/5875000000000000000000000000000 : ℝ)*base75 + (29336847148275487/5875000000000000000000000000000 : ℝ)*base77 + (9876141727474513/5875000000000000000000000000000 : ℝ)*base80 + (55964899311/29375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (21312597/5000000000000000000000 : ℝ)*base90 + (21312597/5000000000000000000000 : ℝ)*base92 + (21312597/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1403_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1403_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1403_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1403_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1403_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
