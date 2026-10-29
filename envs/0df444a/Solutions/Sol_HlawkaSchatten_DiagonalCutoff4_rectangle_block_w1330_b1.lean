-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:52.575173+00:00
-- url     : https://prove2.me/submissions/020ca108-6724-4bf7-b001-1f04d19c96ed

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
theorem support_rectangle_w1330_s3_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052497829/10000000000 : ℝ)*x 0 + (217149207/400000000 : ℝ)*x 1 + (5230065931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052497829/10000000000 : ℝ)^2145 ≤ (6246408566247/50000000000000 : ℝ)^1633 := by
    have hnat : (2052497829 : ℕ)^2145*50000000000000^1633 ≤ 6246408566247^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052497829 10000000000 6246408566247 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217149207/400000000 : ℝ)^2145 ≤ (4482469111527/10000000000000 : ℝ)^1633 := by
    have hnat : (217149207 : ℕ)^2145*10000000000000^1633 ≤ 4482469111527^1633*400000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217149207 400000000 4482469111527 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230065931/10000000000 : ℝ)^2145 ≤ (8536498347163/20000000000000 : ℝ)^1633 := by
    have hnat : (5230065931 : ℕ)^2145*20000000000000^1633 ≤ 8536498347163^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230065931 10000000000 8536498347163 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052497829/10000000000 : ℝ), (217149207/400000000 : ℝ), (5230065931/10000000000 : ℝ)] ![(6246408566247/50000000000000 : ℝ), (4482469111527/10000000000000 : ℝ), (8536498347163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052497829/10000000000 : ℝ)|^2145 ≤ (6246408566247/50000000000000 : ℝ)^1633
        have hw : |(-2052497829/10000000000 : ℝ)|=(2052497829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217149207/400000000 : ℝ)|^2145 ≤ (4482469111527/10000000000000 : ℝ)^1633
        have hw : |(217149207/400000000 : ℝ)|=(217149207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230065931/10000000000 : ℝ)|^2145 ≤ (8536498347163/20000000000000 : ℝ)^1633
        have hw : |(5230065931/10000000000 : ℝ)|=(5230065931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676561003/5000000000 : ℝ)*x 0 + (-430812289/2000000000 : ℝ)*x 1 + (1307516517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676561003/5000000000 : ℝ)^2145 ≤ (11001614722401/25000000000000 : ℝ)^1633 := by
    have hnat : (2676561003 : ℕ)^2145*25000000000000^1633 ≤ 11001614722401^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676561003 5000000000 11001614722401 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430812289/2000000000 : ℝ)^2145 ≤ (13311047890387/100000000000000 : ℝ)^1633 := by
    have hnat : (430812289 : ℕ)^2145*100000000000000^1633 ≤ 13311047890387^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430812289 2000000000 13311047890387 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307516517/2500000000 : ℝ)^2145 ≤ (21341246602209/50000000000000 : ℝ)^1633 := by
    have hnat : (1307516517 : ℕ)^2145*50000000000000^1633 ≤ 21341246602209^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307516517 2500000000 21341246602209 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676561003/5000000000 : ℝ), (-430812289/2000000000 : ℝ), (1307516517/2500000000 : ℝ)] ![(11001614722401/25000000000000 : ℝ), (13311047890387/100000000000000 : ℝ), (21341246602209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676561003/5000000000 : ℝ)|^2145 ≤ (11001614722401/25000000000000 : ℝ)^1633
        have hw : |(2676561003/5000000000 : ℝ)|=(2676561003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430812289/2000000000 : ℝ)|^2145 ≤ (13311047890387/100000000000000 : ℝ)^1633
        have hw : |(-430812289/2000000000 : ℝ)|=(430812289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307516517/2500000000 : ℝ)|^2145 ≤ (21341246602209/50000000000000 : ℝ)^1633
        have hw : |(1307516517/2500000000 : ℝ)|=(1307516517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353121753/10000000000 : ℝ)*x 0 + (5230066363/10000000000 : ℝ)*x 1 + (-134628837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353121753/10000000000 : ℝ)^2145 ≤ (8801291231533/20000000000000 : ℝ)^1633 := by
    have hnat : (5353121753 : ℕ)^2145*20000000000000^1633 ≤ 8801291231533^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353121753 10000000000 8801291231533 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230066363/10000000000 : ℝ)^2145 ≤ (42682496366737/100000000000000 : ℝ)^1633 := by
    have hnat : (5230066363 : ℕ)^2145*100000000000000^1633 ≤ 42682496366737^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230066363 10000000000 42682496366737 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134628837/625000000 : ℝ)^2145 ≤ (6655523730093/50000000000000 : ℝ)^1633 := by
    have hnat : (134628837 : ℕ)^2145*50000000000000^1633 ≤ 6655523730093^1633*625000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134628837 625000000 6655523730093 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353121753/10000000000 : ℝ), (5230066363/10000000000 : ℝ), (-134628837/625000000 : ℝ)] ![(8801291231533/20000000000000 : ℝ), (42682496366737/100000000000000 : ℝ), (6655523730093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353121753/10000000000 : ℝ)|^2145 ≤ (8801291231533/20000000000000 : ℝ)^1633
        have hw : |(5353121753/10000000000 : ℝ)|=(5353121753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230066363/10000000000 : ℝ)|^2145 ≤ (42682496366737/100000000000000 : ℝ)^1633
        have hw : |(5230066363/10000000000 : ℝ)|=(5230066363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134628837/625000000 : ℝ)|^2145 ≤ (6655523730093/50000000000000 : ℝ)^1633
        have hw : |(-134628837/625000000 : ℝ)|=(134628837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4328626531/10000000000 : ℝ)*x 0 + (4126160809/10000000000 : ℝ)*x 1 + (283774951/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328626531/10000000000 : ℝ)^2145 ≤ (16645764517017/50000000000000 : ℝ)^1633 := by
    have hnat : (4328626531 : ℕ)^2145*50000000000000^1633 ≤ 16645764517017^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328626531 10000000000 16645764517017 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126160809/10000000000 : ℝ)^2145 ≤ (31261300193009/100000000000000 : ℝ)^1633 := by
    have hnat : (4126160809 : ℕ)^2145*100000000000000^1633 ≤ 31261300193009^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126160809 10000000000 31261300193009 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283774951/625000000 : ℝ)^2145 ≤ (17723585378561/50000000000000 : ℝ)^1633 := by
    have hnat : (283774951 : ℕ)^2145*50000000000000^1633 ≤ 17723585378561^1633*625000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283774951 625000000 17723585378561 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328626531/10000000000 : ℝ), (4126160809/10000000000 : ℝ), (283774951/625000000 : ℝ)] ![(16645764517017/50000000000000 : ℝ), (31261300193009/100000000000000 : ℝ), (17723585378561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328626531/10000000000 : ℝ)|^2145 ≤ (16645764517017/50000000000000 : ℝ)^1633
        have hw : |(4328626531/10000000000 : ℝ)|=(4328626531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126160809/10000000000 : ℝ)|^2145 ≤ (31261300193009/100000000000000 : ℝ)^1633
        have hw : |(4126160809/10000000000 : ℝ)|=(4126160809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283774951/625000000 : ℝ)|^2145 ≤ (17723585378561/50000000000000 : ℝ)^1633
        have hw : |(283774951/625000000 : ℝ)|=(283774951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052517843/10000000000 : ℝ)*x 0 + (5230899911/10000000000 : ℝ)*x 1 + (1356972773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052517843/10000000000 : ℝ)^2145 ≤ (6246488572393/50000000000000 : ℝ)^1633 := by
    have hnat : (2052517843 : ℕ)^2145*50000000000000^1633 ≤ 6246488572393^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052517843 10000000000 6246488572393 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230899911/10000000000 : ℝ)^2145 ≤ (42691431996959/100000000000000 : ℝ)^1633 := by
    have hnat : (5230899911 : ℕ)^2145*100000000000000^1633 ≤ 42691431996959^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230899911 10000000000 42691431996959 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356972773/2500000000 : ℝ)^2145 ≤ (8963118167873/20000000000000 : ℝ)^1633 := by
    have hnat : (1356972773 : ℕ)^2145*20000000000000^1633 ≤ 8963118167873^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356972773 2500000000 8963118167873 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052517843/10000000000 : ℝ), (5230899911/10000000000 : ℝ), (1356972773/2500000000 : ℝ)] ![(6246488572393/50000000000000 : ℝ), (42691431996959/100000000000000 : ℝ), (8963118167873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052517843/10000000000 : ℝ)|^2145 ≤ (6246488572393/50000000000000 : ℝ)^1633
        have hw : |(-2052517843/10000000000 : ℝ)|=(2052517843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230899911/10000000000 : ℝ)|^2145 ≤ (42691431996959/100000000000000 : ℝ)^1633
        have hw : |(5230899911/10000000000 : ℝ)|=(5230899911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356972773/2500000000 : ℝ)|^2145 ≤ (8963118167873/20000000000000 : ℝ)^1633
        have hw : |(1356972773/2500000000 : ℝ)|=(1356972773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325505003/2500000000 : ℝ)*x 0 + (-978118329/5000000000 : ℝ)*x 1 + (678486411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325505003/2500000000 : ℝ)^2145 ≤ (2715967386399/6250000000000 : ℝ)^1633 := by
    have hnat : (1325505003 : ℕ)^2145*6250000000000^1633 ≤ 2715967386399^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325505003 2500000000 2715967386399 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978118329/5000000000 : ℝ)^2145 ≤ (733058052441/6250000000000 : ℝ)^1633 := by
    have hnat : (978118329 : ℕ)^2145*6250000000000^1633 ≤ 733058052441^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978118329 5000000000 733058052441 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678486411/1250000000 : ℝ)^2145 ≤ (5601949120629/12500000000000 : ℝ)^1633 := by
    have hnat : (678486411 : ℕ)^2145*12500000000000^1633 ≤ 5601949120629^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678486411 1250000000 5601949120629 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325505003/2500000000 : ℝ), (-978118329/5000000000 : ℝ), (678486411/1250000000 : ℝ)] ![(2715967386399/6250000000000 : ℝ), (733058052441/6250000000000 : ℝ), (5601949120629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325505003/2500000000 : ℝ)|^2145 ≤ (2715967386399/6250000000000 : ℝ)^1633
        have hw : |(1325505003/2500000000 : ℝ)|=(1325505003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978118329/5000000000 : ℝ)|^2145 ≤ (733058052441/6250000000000 : ℝ)^1633
        have hw : |(-978118329/5000000000 : ℝ)|=(978118329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678486411/1250000000 : ℝ)|^2145 ≤ (5601949120629/12500000000000 : ℝ)^1633
        have hw : |(678486411/1250000000 : ℝ)|=(678486411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325505421/2500000000 : ℝ)*x 0 + (5427890119/10000000000 : ℝ)*x 1 + (-1956235983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325505421/2500000000 : ℝ)^2145 ≤ (43455496182719/100000000000000 : ℝ)^1633 := by
    have hnat : (1325505421 : ℕ)^2145*100000000000000^1633 ≤ 43455496182719^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325505421 2500000000 43455496182719 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427890119/10000000000 : ℝ)^2145 ≤ (11203895071737/25000000000000 : ℝ)^1633 := by
    have hnat : (5427890119 : ℕ)^2145*25000000000000^1633 ≤ 11203895071737^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427890119 10000000000 11203895071737 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956235983/10000000000 : ℝ)^2145 ≤ (5864461761547/50000000000000 : ℝ)^1633 := by
    have hnat : (1956235983 : ℕ)^2145*50000000000000^1633 ≤ 5864461761547^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956235983 10000000000 5864461761547 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325505421/2500000000 : ℝ), (5427890119/10000000000 : ℝ), (-1956235983/10000000000 : ℝ)] ![(43455496182719/100000000000000 : ℝ), (11203895071737/25000000000000 : ℝ), (5864461761547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325505421/2500000000 : ℝ)|^2145 ≤ (43455496182719/100000000000000 : ℝ)^1633
        have hw : |(1325505421/2500000000 : ℝ)|=(1325505421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427890119/10000000000 : ℝ)|^2145 ≤ (11203895071737/25000000000000 : ℝ)^1633
        have hw : |(5427890119/10000000000 : ℝ)|=(5427890119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956235983/10000000000 : ℝ)|^2145 ≤ (5864461761547/50000000000000 : ℝ)^1633
        have hw : |(-1956235983/10000000000 : ℝ)|=(1956235983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865733771/2000000000 : ℝ)*x 0 + (4538660341/10000000000 : ℝ)*x 1 + (4127909443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865733771/2000000000 : ℝ)^2145 ≤ (33291956608841/100000000000000 : ℝ)^1633 := by
    have hnat : (865733771 : ℕ)^2145*100000000000000^1633 ≤ 33291956608841^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865733771 2000000000 33291956608841 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538660341/10000000000 : ℝ)^2145 ≤ (35429339952743/100000000000000 : ℝ)^1633 := by
    have hnat : (4538660341 : ℕ)^2145*100000000000000^1633 ≤ 35429339952743^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538660341 10000000000 35429339952743 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127909443/10000000000 : ℝ)^2145 ≤ (3909837927409/12500000000000 : ℝ)^1633 := by
    have hnat : (4127909443 : ℕ)^2145*12500000000000^1633 ≤ 3909837927409^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127909443 10000000000 3909837927409 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865733771/2000000000 : ℝ), (4538660341/10000000000 : ℝ), (4127909443/10000000000 : ℝ)] ![(33291956608841/100000000000000 : ℝ), (35429339952743/100000000000000 : ℝ), (3909837927409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865733771/2000000000 : ℝ)|^2145 ≤ (33291956608841/100000000000000 : ℝ)^1633
        have hw : |(865733771/2000000000 : ℝ)|=(865733771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538660341/10000000000 : ℝ)|^2145 ≤ (35429339952743/100000000000000 : ℝ)^1633
        have hw : |(4538660341/10000000000 : ℝ)|=(4538660341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127909443/10000000000 : ℝ)|^2145 ≤ (3909837927409/12500000000000 : ℝ)^1633
        have hw : |(4127909443/10000000000 : ℝ)|=(4127909443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_8 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-84803279/10000000000 : ℝ)*x 0 + (5722910911/10000000000 : ℝ)*x 1 + (1514441401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84803279/10000000000 : ℝ)^2145 ≤ (23758055073/12500000000000 : ℝ)^1633 := by
    have hnat : (84803279 : ℕ)^2145*12500000000000^1633 ≤ 23758055073^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84803279 10000000000 23758055073 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5722910911/10000000000 : ℝ)^2145 ≤ (300263012953/625000000000 : ℝ)^1633 := by
    have hnat : (5722910911 : ℕ)^2145*625000000000^1633 ≤ 300263012953^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5722910911 10000000000 300263012953 625000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514441401/2500000000 : ℝ)^2145 ≤ (25883926737967/50000000000000 : ℝ)^1633 := by
    have hnat : (1514441401 : ℕ)^2145*50000000000000^1633 ≤ 25883926737967^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514441401 2500000000 25883926737967 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84803279/10000000000 : ℝ), (5722910911/10000000000 : ℝ), (1514441401/2500000000 : ℝ)] ![(23758055073/12500000000000 : ℝ), (300263012953/625000000000 : ℝ), (25883926737967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84803279/10000000000 : ℝ)|^2145 ≤ (23758055073/12500000000000 : ℝ)^1633
        have hw : |(-84803279/10000000000 : ℝ)|=(84803279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5722910911/10000000000 : ℝ)|^2145 ≤ (300263012953/625000000000 : ℝ)^1633
        have hw : |(5722910911/10000000000 : ℝ)|=(5722910911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1514441401/2500000000 : ℝ)|^2145 ≤ (25883926737967/50000000000000 : ℝ)^1633
        have hw : |(1514441401/2500000000 : ℝ)|=(1514441401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_9 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (503531521/5000000000 : ℝ)*x 0 + (3482455679/5000000000 : ℝ)*x 1 + (-2145643417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503531521/5000000000 : ℝ)^2145 ≤ (980644606403/20000000000000 : ℝ)^1633 := by
    have hnat : (503531521 : ℕ)^2145*20000000000000^1633 ≤ 980644606403^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503531521 5000000000 980644606403 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3482455679/5000000000 : ℝ)^2145 ≤ (31090978748537/50000000000000 : ℝ)^1633 := by
    have hnat : (3482455679 : ℕ)^2145*50000000000000^1633 ≤ 31090978748537^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3482455679 5000000000 31090978748537 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145643417/5000000000 : ℝ)^2145 ≤ (32914819453347/100000000000000 : ℝ)^1633 := by
    have hnat : (2145643417 : ℕ)^2145*100000000000000^1633 ≤ 32914819453347^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145643417 5000000000 32914819453347 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503531521/5000000000 : ℝ), (3482455679/5000000000 : ℝ), (-2145643417/5000000000 : ℝ)] ![(980644606403/20000000000000 : ℝ), (31090978748537/50000000000000 : ℝ), (32914819453347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503531521/5000000000 : ℝ)|^2145 ≤ (980644606403/20000000000000 : ℝ)^1633
        have hw : |(503531521/5000000000 : ℝ)|=(503531521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3482455679/5000000000 : ℝ)|^2145 ≤ (31090978748537/50000000000000 : ℝ)^1633
        have hw : |(3482455679/5000000000 : ℝ)|=(3482455679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145643417/5000000000 : ℝ)|^2145 ≤ (32914819453347/100000000000000 : ℝ)^1633
        have hw : |(-2145643417/5000000000 : ℝ)|=(2145643417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s3_10 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (463656609/5000000000 : ℝ)*x 0 + (5862290719/10000000000 : ℝ)*x 1 + (5538184169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463656609/5000000000 : ℝ)^2145 ≤ (274977710633/6250000000000 : ℝ)^1633 := by
    have hnat : (463656609 : ℕ)^2145*6250000000000^1633 ≤ 274977710633^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463656609 5000000000 274977710633 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5862290719/10000000000 : ℝ)^2145 ≤ (49584818302603/100000000000000 : ℝ)^1633 := by
    have hnat : (5862290719 : ℕ)^2145*100000000000000^1633 ≤ 49584818302603^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5862290719 10000000000 49584818302603 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5538184169/10000000000 : ℝ)^2145 ≤ (46015538306649/100000000000000 : ℝ)^1633 := by
    have hnat : (5538184169 : ℕ)^2145*100000000000000^1633 ≤ 46015538306649^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538184169 10000000000 46015538306649 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463656609/5000000000 : ℝ), (5862290719/10000000000 : ℝ), (5538184169/10000000000 : ℝ)] ![(274977710633/6250000000000 : ℝ), (49584818302603/100000000000000 : ℝ), (46015538306649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463656609/5000000000 : ℝ)|^2145 ≤ (274977710633/6250000000000 : ℝ)^1633
        have hw : |(463656609/5000000000 : ℝ)|=(463656609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5862290719/10000000000 : ℝ)|^2145 ≤ (49584818302603/100000000000000 : ℝ)^1633
        have hw : |(5862290719/10000000000 : ℝ)|=(5862290719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5538184169/10000000000 : ℝ)|^2145 ≤ (46015538306649/100000000000000 : ℝ)^1633
        have hw : |(5538184169/10000000000 : ℝ)|=(5538184169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5409/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2019/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2443/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2019/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2443/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2019/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2443/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2019/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2443/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2019/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2443/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2019/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2443/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2443/25000 : ℝ) ^ (4289/1024 : ℝ) ≤ (5882600931247631/100000000000000000000 : ℝ) := by
    have hpowers : (2443/25000 : ℝ)^4289 ≤ (5882600931247631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2443 : ℕ)^4289*100000000000000000000^1024 ≤ 5882600931247631^1024*25000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2443 25000 5882600931247631 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2443/25000 : ℝ)) (X := (5882600931247631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2019/12500 : ℝ) ^ (4289/1024 : ℝ) ≤ (48269682211741377/100000000000000000000 : ℝ) := by
    have hpowers : (2019/12500 : ℝ)^4289 ≤ (48269682211741377/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2019 : ℕ)^4289*100000000000000000000^1024 ≤ 48269682211741377^1024*12500^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2019 12500 48269682211741377 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2019/12500 : ℝ)) (X := (48269682211741377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005882600931247631/50000000000000000000 : ℝ) ≤ (625017555122463/625000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50005882600931247631/50000000000000000000 : ℝ)^1024 ≤ (625017555122463/625000000000000 : ℝ)^4289 := by
      have hnat : (50005882600931247631 : ℕ)^1024*625000000000000^4289 ≤ 625017555122463^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005882600931247631 50000000000000000000 625017555122463 625000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017555122463/625000000000000 : ℝ)) (X := (50005882600931247631/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253384517696436813/6250000000000000000 : ℝ) ≤ (5000646310468419/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (6253384517696436813/6250000000000000000 : ℝ)^1024 ≤ (5000646310468419/5000000000000000 : ℝ)^4289 := by
      have hnat : (6253384517696436813 : ℕ)^1024*5000000000000000^4289 ≤ 5000646310468419^4289*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253384517696436813 6250000000000000000 5000646310468419 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646310468419/5000000000000000 : ℝ)) (X := (6253384517696436813/6250000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048269682211741377/50000000000000000000 : ℝ) ≤ (2500576089978567/2500000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50048269682211741377/50000000000000000000 : ℝ)^1024 ≤ (2500576089978567/2500000000000000 : ℝ)^4289 := by
      have hnat : (50048269682211741377 : ℕ)^1024*2500000000000000^4289 ≤ 2500576089978567^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048269682211741377 50000000000000000000 2500576089978567 2500000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500576089978567/2500000000000000 : ℝ)) (X := (50048269682211741377/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5882600931247631/100000000000000000000 : ℝ) ≤ ((797275232504076639/797500000000000000 : ℝ)+2*(101173897743/63800000000000 : ℝ)*(2443/25000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (797275232504076639/797500000000000000 : ℝ)+2*(101173897743/63800000000000 : ℝ)*(2443/25000 : ℝ)=(625017555122463/625000000000000 : ℝ) by norm_num, show 1+2*(5882600931247631/100000000000000000000 : ℝ)=(50005882600931247631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48269682211741377/100000000000000000000 : ℝ)+(5882600931247631/100000000000000000000 : ℝ) ≤ ((797275232504076639/797500000000000000 : ℝ)+(101173897743/63800000000000 : ℝ)*((2019/12500 : ℝ)+(2443/25000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (797275232504076639/797500000000000000 : ℝ)+(101173897743/63800000000000 : ℝ)*((2019/12500 : ℝ)+(2443/25000 : ℝ))=(5000646310468419/5000000000000000 : ℝ) by norm_num, show 1+(48269682211741377/100000000000000000000 : ℝ)+(5882600931247631/100000000000000000000 : ℝ)=(6253384517696436813/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48269682211741377/100000000000000000000 : ℝ) ≤ ((797275232504076639/797500000000000000 : ℝ)+2*(101173897743/63800000000000 : ℝ)*(2019/12500 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (797275232504076639/797500000000000000 : ℝ)+2*(101173897743/63800000000000 : ℝ)*(2019/12500 : ℝ)=(2500576089978567/2500000000000000 : ℝ) by norm_num, show 1+2*(48269682211741377/100000000000000000000 : ℝ)=(50048269682211741377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (797275232504076639/797500000000000000 : ℝ)*(X 1 0+X 2 0)+(101173897743/63800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2443/25000 : ℝ)) (hi := (2019/12500 : ℝ)) (c := (797275232504076639/797500000000000000 : ℝ)) (alpha := (101173897743/63800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (797275232504076639/797500000000000000 : ℝ)*(X 0 1+X 2 1)+(101173897743/63800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2443/25000 : ℝ)) (hi := (2019/12500 : ℝ)) (c := (797275232504076639/797500000000000000 : ℝ)) (alpha := (101173897743/63800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (797275232504076639/797500000000000000 : ℝ)*(X 0 2+X 1 2)+(101173897743/63800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2443/25000 : ℝ)) (hi := (2019/12500 : ℝ)) (c := (797275232504076639/797500000000000000 : ℝ)) (alpha := (101173897743/63800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2052497829/10000000000 : ℝ)*X 0 0+(217149207/400000000 : ℝ)*X 0 1+(5230065931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676561003/5000000000 : ℝ)*X 1 0+(-430812289/2000000000 : ℝ)*X 1 1+(1307516517/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353121753/10000000000 : ℝ)*X 2 0+(5230066363/10000000000 : ℝ)*X 2 1+(-134628837/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328626531/10000000000 : ℝ)*X 0 0+(4126160809/10000000000 : ℝ)*X 0 1+(283774951/625000000 : ℝ)*X 0 2+(4328626531/10000000000 : ℝ)*X 1 0+(4126160809/10000000000 : ℝ)*X 1 1+(283774951/625000000 : ℝ)*X 1 2+(4328626531/10000000000 : ℝ)*X 2 0+(4126160809/10000000000 : ℝ)*X 2 1+(283774951/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2052517843/10000000000 : ℝ)*X 0 0+(5230899911/10000000000 : ℝ)*X 0 1+(1356972773/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325505003/2500000000 : ℝ)*X 1 0+(-978118329/5000000000 : ℝ)*X 1 1+(678486411/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325505421/2500000000 : ℝ)*X 2 0+(5427890119/10000000000 : ℝ)*X 2 1+(-1956235983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865733771/2000000000 : ℝ)*X 0 0+(4538660341/10000000000 : ℝ)*X 0 1+(4127909443/10000000000 : ℝ)*X 0 2+(865733771/2000000000 : ℝ)*X 1 0+(4538660341/10000000000 : ℝ)*X 1 1+(4127909443/10000000000 : ℝ)*X 1 2+(865733771/2000000000 : ℝ)*X 2 0+(4538660341/10000000000 : ℝ)*X 2 1+(4127909443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-84803279/10000000000 : ℝ)*X 0 0+(5722910911/10000000000 : ℝ)*X 0 1+(1514441401/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((503531521/5000000000 : ℝ)*X 2 0+(3482455679/5000000000 : ℝ)*X 2 1+(-2145643417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((463656609/5000000000 : ℝ)*X 0 0+(5862290719/10000000000 : ℝ)*X 0 1+(5538184169/10000000000 : ℝ)*X 0 2+(463656609/5000000000 : ℝ)*X 1 0+(5862290719/10000000000 : ℝ)*X 1 1+(5538184169/10000000000 : ℝ)*X 1 2+(463656609/5000000000 : ℝ)*X 2 0+(5862290719/10000000000 : ℝ)*X 2 1+(5538184169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s3_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2917005546999904387759881/498437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1458037/4000000000000 : ℝ)*(lower2) + (122607887/50000000000000 : ℝ)*(lower4) + (23274066758183/625000000000 : ℝ)*(major0) + (23274066758183/625000000000 : ℝ)*(major1) + (23274066758183/625000000000 : ℝ)*(major2) + (5033627157500221/100000000000000 : ℝ)*(sp0) + (100672504245473/2000000000000 : ℝ)*(sp1) + (5033628659002741/100000000000000 : ℝ)*(sp2) + (603517917564259/25000000000000 : ℝ)*(sp3) + (3287219/12500000000000 : ℝ)*(sp4) + (1838648027/50000000000000 : ℝ)*(sp5) + (607715163/100000000000000 : ℝ)*(sp7) + (170577173/10000000000000 : ℝ)*(sp8) + (115283481/50000000000000 : ℝ)*(sp9) + (2414072277972199/100000000000000 : ℝ)*(f.failure) + (5033628889569703/100000000000000 : ℝ)*(f.sum) + (18426650379/6380000000000000000000000 : ℝ)*base66 + (7670927700443187/498437500000000000000000000000 : ℝ)*base67 + (3059348383936937/498437500000000000000000000000 : ℝ)*base69 + (11505261901785501/996875000000000000000000000000 : ℝ)*base72 + (410293980429/319000000000000000000000000 : ℝ)*base73 + (2298856292426999/996875000000000000000000000000 : ℝ)*base75 + (1409108386701281/249218750000000000000000000000 : ℝ)*base77 + (1414093154783453/124609375000000000000000000000 : ℝ)*base79 + (340770235891/319000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (23694627/10000000000000000000000 : ℝ)*base89 + (23694627/10000000000000000000000 : ℝ)*base91 + (23694627/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187270363858885871331/63800000000000000000000000 : ℝ) := by norm_num
    linear_combination (165483221/100000000000000 : ℝ)*(lower2) + (187774437648417/5000000000000 : ℝ)*(major0) + (187774437648417/5000000000000 : ℝ)*(major1) + (187774437648417/5000000000000 : ℝ)*(major2) + (42493263/500000000000 : ℝ)*(sp0) + (1784853821/20000000000000 : ℝ)*(sp1) + (1554417551/25000000000000 : ℝ)*(sp3) + (1015277014852983/20000000000000 : ℝ)*(sp4) + (5076386094611399/100000000000000 : ℝ)*(sp5) + (2538196767075443/50000000000000 : ℝ)*(sp6) + (304321952159711/12500000000000 : ℝ)*(sp7) + (144596299/10000000000000 : ℝ)*(sp8) + (1484729619/100000000000000 : ℝ)*(sp9) + (554265873/100000000000000 : ℝ)*(sp10) + (486916477842753/20000000000000 : ℝ)*(f.failure) + (634549377360063/12500000000000 : ℝ)*(f.sum) + (42007099151/12760000000000000000000000 : ℝ)*base66 + (20217523381242963/3987500000000000000000000000000 : ℝ)*base67 + (19922905591980463/3987500000000000000000000000000 : ℝ)*base69 + (32785766460117963/3987500000000000000000000000000 : ℝ)*base71 + (183239908377/159500000000000000000000000 : ℝ)*base74 + (1683830939619537/3987500000000000000000000000000 : ℝ)*base76 + (16877396060832037/3987500000000000000000000000000 : ℝ)*base78 + (15699071735494537/3987500000000000000000000000000 : ℝ)*base80 + (820599846543/319000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5013669/2000000000000000000000 : ℝ)*base89 + (5013669/2000000000000000000000 : ℝ)*base91 + (5013669/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s4_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054056983/10000000000 : ℝ)*x 0 + (5416108879/10000000000 : ℝ)*x 1 + (2620831973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054056983/10000000000 : ℝ)^2145 ≤ (6252642031057/50000000000000 : ℝ)^1633 := by
    have hnat : (2054056983 : ℕ)^2145*50000000000000^1633 ≤ 6252642031057^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054056983 10000000000 6252642031057 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416108879/10000000000 : ℝ)^2145 ≤ (2792990839487/6250000000000 : ℝ)^1633 := by
    have hnat : (5416108879 : ℕ)^2145*6250000000000^1633 ≤ 2792990839487^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416108879 10000000000 2792990839487 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620831973/5000000000 : ℝ)^2145 ≤ (21403431243107/50000000000000 : ℝ)^1633 := by
    have hnat : (2620831973 : ℕ)^2145*50000000000000^1633 ≤ 21403431243107^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620831973 5000000000 21403431243107 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054056983/10000000000 : ℝ), (5416108879/10000000000 : ℝ), (2620831973/5000000000 : ℝ)] ![(6252642031057/50000000000000 : ℝ), (2792990839487/6250000000000 : ℝ), (21403431243107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054056983/10000000000 : ℝ)|^2145 ≤ (6252642031057/50000000000000 : ℝ)^1633
        have hw : |(-2054056983/10000000000 : ℝ)|=(2054056983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416108879/10000000000 : ℝ)|^2145 ≤ (2792990839487/6250000000000 : ℝ)^1633
        have hw : |(5416108879/10000000000 : ℝ)|=(5416108879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620831973/5000000000 : ℝ)|^2145 ≤ (21403431243107/50000000000000 : ℝ)^1633
        have hw : |(2620831973/5000000000 : ℝ)|=(2620831973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349911909/10000000000 : ℝ)*x 0 + (-428600143/2000000000 : ℝ)*x 1 + (5241663777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349911909/10000000000 : ℝ)^2145 ≤ (43971798956969/100000000000000 : ℝ)^1633 := by
    have hnat : (5349911909 : ℕ)^2145*100000000000000^1633 ≤ 43971798956969^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349911909 10000000000 43971798956969 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428600143/2000000000 : ℝ)^2145 ≤ (2644268071431/20000000000000 : ℝ)^1633 := by
    have hnat : (428600143 : ℕ)^2145*20000000000000^1633 ≤ 2644268071431^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428600143 2000000000 2644268071431 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241663777/10000000000 : ℝ)^2145 ≤ (21403430336661/50000000000000 : ℝ)^1633 := by
    have hnat : (5241663777 : ℕ)^2145*50000000000000^1633 ≤ 21403430336661^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241663777 10000000000 21403430336661 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349911909/10000000000 : ℝ), (-428600143/2000000000 : ℝ), (5241663777/10000000000 : ℝ)] ![(43971798956969/100000000000000 : ℝ), (2644268071431/20000000000000 : ℝ), (21403430336661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349911909/10000000000 : ℝ)|^2145 ≤ (43971798956969/100000000000000 : ℝ)^1633
        have hw : |(5349911909/10000000000 : ℝ)|=(5349911909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428600143/2000000000 : ℝ)|^2145 ≤ (2644268071431/20000000000000 : ℝ)^1633
        have hw : |(-428600143/2000000000 : ℝ)|=(428600143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241663777/10000000000 : ℝ)|^2145 ≤ (21403430336661/50000000000000 : ℝ)^1633
        have hw : |(5241663777/10000000000 : ℝ)|=(5241663777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349911987/10000000000 : ℝ)*x 0 + (1310415887/2500000000 : ℝ)*x 1 + (-1071500457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349911987/10000000000 : ℝ)^2145 ≤ (10992949949767/25000000000000 : ℝ)^1633 := by
    have hnat : (5349911987 : ℕ)^2145*25000000000000^1633 ≤ 10992949949767^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349911987 10000000000 10992949949767 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310415887/2500000000 : ℝ)^2145 ≤ (42806858216799/100000000000000 : ℝ)^1633 := by
    have hnat : (1310415887 : ℕ)^2145*100000000000000^1633 ≤ 42806858216799^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310415887 2500000000 42806858216799 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071500457/5000000000 : ℝ)^2145 ≤ (13221341969831/100000000000000 : ℝ)^1633 := by
    have hnat : (1071500457 : ℕ)^2145*100000000000000^1633 ≤ 13221341969831^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071500457 5000000000 13221341969831 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349911987/10000000000 : ℝ), (1310415887/2500000000 : ℝ), (-1071500457/5000000000 : ℝ)] ![(10992949949767/25000000000000 : ℝ), (42806858216799/100000000000000 : ℝ), (13221341969831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349911987/10000000000 : ℝ)|^2145 ≤ (10992949949767/25000000000000 : ℝ)^1633
        have hw : |(5349911987/10000000000 : ℝ)|=(5349911987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310415887/2500000000 : ℝ)|^2145 ≤ (42806858216799/100000000000000 : ℝ)^1633
        have hw : |(1310415887/2500000000 : ℝ)|=(1310415887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071500457/5000000000 : ℝ)|^2145 ≤ (13221341969831/100000000000000 : ℝ)^1633
        have hw : |(-1071500457/5000000000 : ℝ)|=(1071500457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4329573457/10000000000 : ℝ)*x 0 + (129727891/312500000 : ℝ)*x 1 + (4515031759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329573457/10000000000 : ℝ)^2145 ≤ (33301095591199/100000000000000 : ℝ)^1633 := by
    have hnat : (4329573457 : ℕ)^2145*100000000000000^1633 ≤ 33301095591199^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329573457 10000000000 33301095591199 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129727891/312500000 : ℝ)^2145 ≤ (1575582228023/5000000000000 : ℝ)^1633 := by
    have hnat : (129727891 : ℕ)^2145*5000000000000^1633 ≤ 1575582228023^1633*312500000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129727891 312500000 1575582228023 5000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515031759/10000000000 : ℝ)^2145 ≤ (35187259826317/100000000000000 : ℝ)^1633 := by
    have hnat : (4515031759 : ℕ)^2145*100000000000000^1633 ≤ 35187259826317^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515031759 10000000000 35187259826317 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329573457/10000000000 : ℝ), (129727891/312500000 : ℝ), (4515031759/10000000000 : ℝ)] ![(33301095591199/100000000000000 : ℝ), (1575582228023/5000000000000 : ℝ), (35187259826317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329573457/10000000000 : ℝ)|^2145 ≤ (33301095591199/100000000000000 : ℝ)^1633
        have hw : |(4329573457/10000000000 : ℝ)|=(4329573457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129727891/312500000 : ℝ)|^2145 ≤ (1575582228023/5000000000000 : ℝ)^1633
        have hw : |(129727891/312500000 : ℝ)|=(129727891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515031759/10000000000 : ℝ)|^2145 ≤ (35187259826317/100000000000000 : ℝ)^1633
        have hw : |(4515031759/10000000000 : ℝ)|=(4515031759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-410814123/2000000000 : ℝ)*x 0 + (2621153657/5000000000 : ℝ)*x 1 + (2707730999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410814123/2000000000 : ℝ)^2145 ≤ (12505393076099/100000000000000 : ℝ)^1633 := by
    have hnat : (410814123 : ℕ)^2145*100000000000000^1633 ≤ 12505393076099^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410814123 2000000000 12505393076099 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621153657/5000000000 : ℝ)^2145 ≤ (10703441034913/25000000000000 : ℝ)^1633 := by
    have hnat : (2621153657 : ℕ)^2145*25000000000000^1633 ≤ 10703441034913^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621153657 5000000000 10703441034913 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707730999/5000000000 : ℝ)^2145 ≤ (4468084276247/10000000000000 : ℝ)^1633 := by
    have hnat : (2707730999 : ℕ)^2145*10000000000000^1633 ≤ 4468084276247^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707730999 5000000000 4468084276247 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410814123/2000000000 : ℝ), (2621153657/5000000000 : ℝ), (2707730999/5000000000 : ℝ)] ![(12505393076099/100000000000000 : ℝ), (10703441034913/25000000000000 : ℝ), (4468084276247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410814123/2000000000 : ℝ)|^2145 ≤ (12505393076099/100000000000000 : ℝ)^1633
        have hw : |(-410814123/2000000000 : ℝ)|=(410814123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621153657/5000000000 : ℝ)|^2145 ≤ (10703441034913/25000000000000 : ℝ)^1633
        have hw : |(2621153657/5000000000 : ℝ)|=(2621153657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707730999/5000000000 : ℝ)|^2145 ≤ (4468084276247/10000000000000 : ℝ)^1633
        have hw : |(2707730999/5000000000 : ℝ)|=(2707730999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305041423/10000000000 : ℝ)*x 0 + (-984601321/5000000000 : ℝ)*x 1 + (2707730999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305041423/10000000000 : ℝ)^2145 ≤ (8697601768549/20000000000000 : ℝ)^1633 := by
    have hnat : (5305041423 : ℕ)^2145*20000000000000^1633 ≤ 8697601768549^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305041423 10000000000 8697601768549 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984601321/5000000000 : ℝ)^2145 ≤ (1183114837163/10000000000000 : ℝ)^1633 := by
    have hnat : (984601321 : ℕ)^2145*10000000000000^1633 ≤ 1183114837163^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984601321 5000000000 1183114837163 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707730999/5000000000 : ℝ)^2145 ≤ (4468084276247/10000000000000 : ℝ)^1633 := by
    have hnat : (2707730999 : ℕ)^2145*10000000000000^1633 ≤ 4468084276247^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707730999 5000000000 4468084276247 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305041423/10000000000 : ℝ), (-984601321/5000000000 : ℝ), (2707730999/5000000000 : ℝ)] ![(8697601768549/20000000000000 : ℝ), (1183114837163/10000000000000 : ℝ), (4468084276247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305041423/10000000000 : ℝ)|^2145 ≤ (8697601768549/20000000000000 : ℝ)^1633
        have hw : |(5305041423/10000000000 : ℝ)|=(5305041423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984601321/5000000000 : ℝ)|^2145 ≤ (1183114837163/10000000000000 : ℝ)^1633
        have hw : |(-984601321/5000000000 : ℝ)|=(984601321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707730999/5000000000 : ℝ)|^2145 ≤ (4468084276247/10000000000000 : ℝ)^1633
        have hw : |(2707730999/5000000000 : ℝ)|=(2707730999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305041437/10000000000 : ℝ)*x 0 + (270773099/500000000 : ℝ)*x 1 + (-246150331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305041437/10000000000 : ℝ)^2145 ≤ (10872002248373/25000000000000 : ℝ)^1633 := by
    have hnat : (5305041437 : ℕ)^2145*25000000000000^1633 ≤ 10872002248373^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305041437 10000000000 10872002248373 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270773099/500000000 : ℝ)^2145 ≤ (11170210641849/25000000000000 : ℝ)^1633 := by
    have hnat : (270773099 : ℕ)^2145*25000000000000^1633 ≤ 11170210641849^1633*500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270773099 500000000 11170210641849 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246150331/1250000000 : ℝ)^2145 ≤ (11831148418981/100000000000000 : ℝ)^1633 := by
    have hnat : (246150331 : ℕ)^2145*100000000000000^1633 ≤ 11831148418981^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246150331 1250000000 11831148418981 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305041437/10000000000 : ℝ), (270773099/500000000 : ℝ), (-246150331/1250000000 : ℝ)] ![(10872002248373/25000000000000 : ℝ), (11170210641849/25000000000000 : ℝ), (11831148418981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305041437/10000000000 : ℝ)|^2145 ≤ (10872002248373/25000000000000 : ℝ)^1633
        have hw : |(5305041437/10000000000 : ℝ)|=(5305041437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270773099/500000000 : ℝ)|^2145 ≤ (11170210641849/25000000000000 : ℝ)^1633
        have hw : |(270773099/500000000 : ℝ)|=(270773099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246150331/1250000000 : ℝ)|^2145 ≤ (11831148418981/100000000000000 : ℝ)^1633
        have hw : |(-246150331/1250000000 : ℝ)|=(246150331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s4_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (54120019/125000000 : ℝ)*x 0 + (56421123/125000000 : ℝ)*x 1 + (4152641671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54120019/125000000 : ℝ)^2145 ≤ (33301379114697/100000000000000 : ℝ)^1633 := by
    have hnat : (54120019 : ℕ)^2145*100000000000000^1633 ≤ 33301379114697^1633*125000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54120019 125000000 33301379114697 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56421123/125000000 : ℝ)^2145 ≤ (35173523461537/100000000000000 : ℝ)^1633 := by
    have hnat : (56421123 : ℕ)^2145*100000000000000^1633 ≤ 35173523461537^1633*125000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56421123 125000000 35173523461537 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152641671/10000000000 : ℝ)^2145 ≤ (31525097404401/100000000000000 : ℝ)^1633 := by
    have hnat : (4152641671 : ℕ)^2145*100000000000000^1633 ≤ 31525097404401^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152641671 10000000000 31525097404401 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54120019/125000000 : ℝ), (56421123/125000000 : ℝ), (4152641671/10000000000 : ℝ)] ![(33301379114697/100000000000000 : ℝ), (35173523461537/100000000000000 : ℝ), (31525097404401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54120019/125000000 : ℝ)|^2145 ≤ (33301379114697/100000000000000 : ℝ)^1633
        have hw : |(54120019/125000000 : ℝ)|=(54120019/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56421123/125000000 : ℝ)|^2145 ≤ (35173523461537/100000000000000 : ℝ)^1633
        have hw : |(56421123/125000000 : ℝ)|=(56421123/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152641671/10000000000 : ℝ)|^2145 ≤ (31525097404401/100000000000000 : ℝ)^1633
        have hw : |(4152641671/10000000000 : ℝ)|=(4152641671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2213/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5409/50000 : ℝ) ^ (4289/1024 : ℝ) ≤ (4503158726097551/50000000000000000000 : ℝ) := by
    have hpowers : (5409/50000 : ℝ)^4289 ≤ (4503158726097551/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5409 : ℕ)^4289*50000000000000000000^1024 ≤ 4503158726097551^1024*50000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5409 50000 4503158726097551 50000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5409/50000 : ℝ)) (X := (4503158726097551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15021/100000 : ℝ) ^ (4289/1024 : ℝ) ≤ (35614136022724149/100000000000000000000 : ℝ) := by
    have hpowers : (15021/100000 : ℝ)^4289 ≤ (35614136022724149/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15021 : ℕ)^4289*100000000000000000000^1024 ≤ 35614136022724149^1024*100000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15021 100000 35614136022724149 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15021/100000 : ℝ)) (X := (35614136022724149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004503158726097551/25000000000000000000 : ℝ) ≤ (5000215011350903/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (25004503158726097551/25000000000000000000 : ℝ)^1024 ≤ (5000215011350903/5000000000000000 : ℝ)^4289 := by
      have hnat : (25004503158726097551 : ℕ)^1024*5000000000000000^4289 ≤ 5000215011350903^4289*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004503158726097551 25000000000000000000 5000215011350903 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215011350903/5000000000000000 : ℝ)) (X := (25004503158726097551/25000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044620453474919251/100000000000000000000 : ℝ) ≤ (10001065133745183/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (100044620453474919251/100000000000000000000 : ℝ)^1024 ≤ (10001065133745183/10000000000000000 : ℝ)^4289 := by
      have hnat : (100044620453474919251 : ℕ)^1024*10000000000000000^4289 ≤ 10001065133745183^4289*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044620453474919251 100000000000000000000 10001065133745183 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001065133745183/10000000000000000 : ℝ)) (X := (100044620453474919251/100000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035614136022724149/50000000000000000000 : ℝ) ≤ (125021253059857/125000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50035614136022724149/50000000000000000000 : ℝ)^1024 ≤ (125021253059857/125000000000000 : ℝ)^4289 := by
      have hnat : (50035614136022724149 : ℕ)^1024*125000000000000^4289 ≤ 125021253059857^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035614136022724149 50000000000000000000 125021253059857 125000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125021253059857/125000000000000 : ℝ)) (X := (50035614136022724149/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4503158726097551/50000000000000000000 : ℝ) ≤ ((2334337006826732547/2335000000000000000 : ℝ)+2*(635111043377/420300000000000 : ℝ)*(5409/50000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (2334337006826732547/2335000000000000000 : ℝ)+2*(635111043377/420300000000000 : ℝ)*(5409/50000 : ℝ)=(5000215011350903/5000000000000000 : ℝ) by norm_num, show 1+2*(4503158726097551/50000000000000000000 : ℝ)=(25004503158726097551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35614136022724149/100000000000000000000 : ℝ)+(4503158726097551/50000000000000000000 : ℝ) ≤ ((2334337006826732547/2335000000000000000 : ℝ)+(635111043377/420300000000000 : ℝ)*((15021/100000 : ℝ)+(5409/50000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (2334337006826732547/2335000000000000000 : ℝ)+(635111043377/420300000000000 : ℝ)*((15021/100000 : ℝ)+(5409/50000 : ℝ))=(10001065133745183/10000000000000000 : ℝ) by norm_num, show 1+(35614136022724149/100000000000000000000 : ℝ)+(4503158726097551/50000000000000000000 : ℝ)=(100044620453474919251/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35614136022724149/100000000000000000000 : ℝ) ≤ ((2334337006826732547/2335000000000000000 : ℝ)+2*(635111043377/420300000000000 : ℝ)*(15021/100000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (2334337006826732547/2335000000000000000 : ℝ)+2*(635111043377/420300000000000 : ℝ)*(15021/100000 : ℝ)=(125021253059857/125000000000000 : ℝ) by norm_num, show 1+2*(35614136022724149/100000000000000000000 : ℝ)=(50035614136022724149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2334337006826732547/2335000000000000000 : ℝ)*(X 1 0+X 2 0)+(635111043377/420300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15021/100000 : ℝ)) (c := (2334337006826732547/2335000000000000000 : ℝ)) (alpha := (635111043377/420300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2334337006826732547/2335000000000000000 : ℝ)*(X 0 1+X 2 1)+(635111043377/420300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15021/100000 : ℝ)) (c := (2334337006826732547/2335000000000000000 : ℝ)) (alpha := (635111043377/420300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2334337006826732547/2335000000000000000 : ℝ)*(X 0 2+X 1 2)+(635111043377/420300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15021/100000 : ℝ)) (c := (2334337006826732547/2335000000000000000 : ℝ)) (alpha := (635111043377/420300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2054056983/10000000000 : ℝ)*X 0 0+(5416108879/10000000000 : ℝ)*X 0 1+(2620831973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349911909/10000000000 : ℝ)*X 1 0+(-428600143/2000000000 : ℝ)*X 1 1+(5241663777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349911987/10000000000 : ℝ)*X 2 0+(1310415887/2500000000 : ℝ)*X 2 1+(-1071500457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329573457/10000000000 : ℝ)*X 0 0+(129727891/312500000 : ℝ)*X 0 1+(4515031759/10000000000 : ℝ)*X 0 2+(4329573457/10000000000 : ℝ)*X 1 0+(129727891/312500000 : ℝ)*X 1 1+(4515031759/10000000000 : ℝ)*X 1 2+(4329573457/10000000000 : ℝ)*X 2 0+(129727891/312500000 : ℝ)*X 2 1+(4515031759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410814123/2000000000 : ℝ)*X 0 0+(2621153657/5000000000 : ℝ)*X 0 1+(2707730999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305041423/10000000000 : ℝ)*X 1 0+(-984601321/5000000000 : ℝ)*X 1 1+(2707730999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305041437/10000000000 : ℝ)*X 2 0+(270773099/500000000 : ℝ)*X 2 1+(-246150331/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54120019/125000000 : ℝ)*X 0 0+(56421123/125000000 : ℝ)*X 0 1+(4152641671/10000000000 : ℝ)*X 0 2+(54120019/125000000 : ℝ)*X 1 0+(56421123/125000000 : ℝ)*X 1 1+(4152641671/10000000000 : ℝ)*X 1 2+(54120019/125000000 : ℝ)*X 2 0+(56421123/125000000 : ℝ)*X 2 1+(4152641671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1730379805998005413323082529/175125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2122736129/100000000000000 : ℝ)*(base19) + (1001450263/50000000000000 : ℝ)*(base23) + (67788667/50000000000000 : ℝ)*(lower2) + (372189099/100000000000000 : ℝ)*(upper3) + (1337627/5000000000000 : ℝ)*(lower4) + (2120450876188877/50000000000000 : ℝ)*(major0) + (2120450876188877/50000000000000 : ℝ)*(major1) + (2120450876188877/50000000000000 : ℝ)*(major2) + (573250946128997/10000000000000 : ℝ)*(sp0) + (716567308330811/12500000000000 : ℝ)*(sp1) + (1433134646620523/25000000000000 : ℝ)*(sp2) + (687309773350081/25000000000000 : ℝ)*(sp3) + (31128092647/100000000000000 : ℝ)*(sp4) + (4698522333/20000000000000 : ℝ)*(sp7) + (687315646502997/25000000000000 : ℝ)*(f.failure) + (5732540589382617/100000000000000 : ℝ)*(f.sum) + (193297541785463/21015000000000000000000000000 : ℝ)*base65 + (1375679805541967471/1050750000000000000000000000000000 : ℝ)*base67 + (7462137432106217471/1050750000000000000000000000000000 : ℝ)*base69 + (1552061889046032529/1050750000000000000000000000000000 : ℝ)*base72 + (25517897935631/10507500000000000000000000000 : ℝ)*base74 + (7082065553468717471/1050750000000000000000000000000000 : ℝ)*base75 + (4009125779944967471/1050750000000000000000000000000000 : ℝ)*base77 + (19264011867829032529/1050750000000000000000000000000000 : ℝ)*base80 + (31329733681613/21015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (348919/2500000000000000000000 : ℝ)*base90 + (348919/2500000000000000000000 : ℝ)*base92 + (348919/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32165537330501926385628821/3648437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (195711067/12500000000000 : ℝ)*(base19) + (1700736953/100000000000000 : ℝ)*(base23) + (9006807/5000000000000 : ℝ)*(upper3) + (556387/1000000000000 : ℝ)*(lower4) + (47174619/25000000000000 : ℝ)*(upper5) + (66756998007303/1562500000000 : ℝ)*(major0) + (66756998007303/1562500000000 : ℝ)*(major1) + (66756998007303/1562500000000 : ℝ)*(major2) + (1237434349/4000000000000 : ℝ)*(sp1) + (16350422797/50000000000000 : ℝ)*(sp2) + (1443795590884121/25000000000000 : ℝ)*(sp4) + (2887574930994611/50000000000000 : ℝ)*(sp5) + (5775147961953937/100000000000000 : ℝ)*(sp6) + (276971308752329/10000000000000 : ℝ)*(sp7) + (276971308752329/10000000000000 : ℝ)*(f.failure) + (1443795590884121/25000000000000 : ℝ)*(f.sum) + (4327836218693/1751250000000000000000000000 : ℝ)*base66 + (36788072492909723/10945312500000000000000000000000 : ℝ)*base67 + (13412734687845269/1368164062500000000000000000000 : ℝ)*base70 + (88558567500977429/21890625000000000000000000000000 : ℝ)*base72 + (6996862810423/7005000000000000000000000000 : ℝ)*base73 + (318215045878085071/21890625000000000000000000000000 : ℝ)*base75 + (82832501348102429/21890625000000000000000000000000 : ℝ)*base78 + (228110148547684027/10945312500000000000000000000000 : ℝ)*base80 + (14165582531281/3502500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5911117/1000000000000000000000 : ℝ)*base89 + (5911117/1000000000000000000000 : ℝ)*base91 + (5911117/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s5_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-410866287/2000000000 : ℝ)*x 0 + (676719807/1250000000 : ℝ)*x 1 + (2621916857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410866287/2000000000 : ℝ)^2145 ≤ (12507478875913/100000000000000 : ℝ)^1633 := by
    have hnat : (410866287 : ℕ)^2145*100000000000000^1633 ≤ 12507478875913^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410866287 2000000000 12507478875913 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676719807/1250000000 : ℝ)^2145 ≤ (5582797703521/12500000000000 : ℝ)^1633 := by
    have hnat : (676719807 : ℕ)^2145*12500000000000^1633 ≤ 5582797703521^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676719807 1250000000 5582797703521 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621916857/5000000000 : ℝ)^2145 ≤ (42830139475909/100000000000000 : ℝ)^1633 := by
    have hnat : (2621916857 : ℕ)^2145*100000000000000^1633 ≤ 42830139475909^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621916857 5000000000 42830139475909 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410866287/2000000000 : ℝ), (676719807/1250000000 : ℝ), (2621916857/5000000000 : ℝ)] ![(12507478875913/100000000000000 : ℝ), (5582797703521/12500000000000 : ℝ), (42830139475909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410866287/2000000000 : ℝ)|^2145 ≤ (12507478875913/100000000000000 : ℝ)^1633
        have hw : |(-410866287/2000000000 : ℝ)|=(410866287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676719807/1250000000 : ℝ)|^2145 ≤ (5582797703521/12500000000000 : ℝ)^1633
        have hw : |(676719807/1250000000 : ℝ)|=(676719807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621916857/5000000000 : ℝ)|^2145 ≤ (42830139475909/100000000000000 : ℝ)^1633
        have hw : |(2621916857/5000000000 : ℝ)|=(2621916857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337328087/2500000000 : ℝ)*x 0 + (-2140926223/10000000000 : ℝ)*x 1 + (524383399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337328087/2500000000 : ℝ)^2145 ≤ (21982663061559/50000000000000 : ℝ)^1633 := by
    have hnat : (1337328087 : ℕ)^2145*50000000000000^1633 ≤ 21982663061559^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337328087 2500000000 21982663061559 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140926223/10000000000 : ℝ)^2145 ≤ (13204531425179/100000000000000 : ℝ)^1633 := by
    have hnat : (2140926223 : ℕ)^2145*100000000000000^1633 ≤ 13204531425179^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140926223 10000000000 13204531425179 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524383399/1000000000 : ℝ)^2145 ≤ (21415071218497/50000000000000 : ℝ)^1633 := by
    have hnat : (524383399 : ℕ)^2145*50000000000000^1633 ≤ 21415071218497^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524383399 1000000000 21415071218497 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337328087/2500000000 : ℝ), (-2140926223/10000000000 : ℝ), (524383399/1000000000 : ℝ)] ![(21982663061559/50000000000000 : ℝ), (13204531425179/100000000000000 : ℝ), (21415071218497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337328087/2500000000 : ℝ)|^2145 ≤ (21982663061559/50000000000000 : ℝ)^1633
        have hw : |(1337328087/2500000000 : ℝ)|=(1337328087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140926223/10000000000 : ℝ)|^2145 ≤ (13204531425179/100000000000000 : ℝ)^1633
        have hw : |(-2140926223/10000000000 : ℝ)|=(2140926223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524383399/1000000000 : ℝ)|^2145 ≤ (21415071218497/50000000000000 : ℝ)^1633
        have hw : |(524383399/1000000000 : ℝ)|=(524383399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668663943/1250000000 : ℝ)*x 0 + (131095859/250000000 : ℝ)*x 1 + (-535231701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668663943/1250000000 : ℝ)^2145 ≤ (21982658721661/50000000000000 : ℝ)^1633 := by
    have hnat : (668663943 : ℕ)^2145*50000000000000^1633 ≤ 21982658721661^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668663943 1250000000 21982658721661 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131095859/250000000 : ℝ)^2145 ≤ (42830146406563/100000000000000 : ℝ)^1633 := by
    have hnat : (131095859 : ℕ)^2145*100000000000000^1633 ≤ 42830146406563^1633*250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131095859 250000000 42830146406563 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535231701/2500000000 : ℝ)^2145 ≤ (6602268066059/50000000000000 : ℝ)^1633 := by
    have hnat : (535231701 : ℕ)^2145*50000000000000^1633 ≤ 6602268066059^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535231701 2500000000 6602268066059 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668663943/1250000000 : ℝ), (131095859/250000000 : ℝ), (-535231701/2500000000 : ℝ)] ![(21982658721661/50000000000000 : ℝ), (42830146406563/100000000000000 : ℝ), (6602268066059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668663943/1250000000 : ℝ)|^2145 ≤ (21982658721661/50000000000000 : ℝ)^1633
        have hw : |(668663943/1250000000 : ℝ)|=(668663943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131095859/250000000 : ℝ)|^2145 ≤ (42830146406563/100000000000000 : ℝ)^1633
        have hw : |(131095859/250000000 : ℝ)|=(131095859/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535231701/2500000000 : ℝ)|^2145 ≤ (6602268066059/50000000000000 : ℝ)^1633
        have hw : |(-535231701/2500000000 : ℝ)|=(535231701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082433981/2500000000 : ℝ)*x 0 + (1038996467/2500000000 : ℝ)*x 1 + (2255149227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082433981/2500000000 : ℝ)^2145 ≤ (33302737020709/100000000000000 : ℝ)^1633 := by
    have hnat : (1082433981 : ℕ)^2145*100000000000000^1633 ≤ 33302737020709^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082433981 2500000000 33302737020709 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038996467/2500000000 : ℝ)^2145 ≤ (31558449241351/100000000000000 : ℝ)^1633 := by
    have hnat : (1038996467 : ℕ)^2145*100000000000000^1633 ≤ 31558449241351^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038996467 2500000000 31558449241351 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255149227/5000000000 : ℝ)^2145 ≤ (8784703430977/25000000000000 : ℝ)^1633 := by
    have hnat : (2255149227 : ℕ)^2145*25000000000000^1633 ≤ 8784703430977^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255149227 5000000000 8784703430977 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082433981/2500000000 : ℝ), (1038996467/2500000000 : ℝ), (2255149227/5000000000 : ℝ)] ![(33302737020709/100000000000000 : ℝ), (31558449241351/100000000000000 : ℝ), (8784703430977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082433981/2500000000 : ℝ)|^2145 ≤ (33302737020709/100000000000000 : ℝ)^1633
        have hw : |(1082433981/2500000000 : ℝ)|=(1082433981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038996467/2500000000 : ℝ)|^2145 ≤ (31558449241351/100000000000000 : ℝ)^1633
        have hw : |(1038996467/2500000000 : ℝ)|=(1038996467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255149227/5000000000 : ℝ)|^2145 ≤ (8784703430977/25000000000000 : ℝ)^1633
        have hw : |(2255149227/5000000000 : ℝ)|=(2255149227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51358591/250000000 : ℝ)*x 0 + (5244444731/10000000000 : ℝ)*x 1 + (5413144489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51358591/250000000 : ℝ)^2145 ≤ (6253788241187/50000000000000 : ℝ)^1633 := by
    have hnat : (51358591 : ℕ)^2145*50000000000000^1633 ≤ 6253788241187^1633*250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51358591 250000000 6253788241187 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244444731/10000000000 : ℝ)^2145 ≤ (1070917373301/2500000000000 : ℝ)^1633 := by
    have hnat : (5244444731 : ℕ)^2145*2500000000000^1633 ≤ 1070917373301^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244444731 10000000000 1070917373301 2500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413144489/10000000000 : ℝ)^2145 ≤ (44655728568439/100000000000000 : ℝ)^1633 := by
    have hnat : (5413144489 : ℕ)^2145*100000000000000^1633 ≤ 44655728568439^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413144489 10000000000 44655728568439 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51358591/250000000 : ℝ), (5244444731/10000000000 : ℝ), (5413144489/10000000000 : ℝ)] ![(6253788241187/50000000000000 : ℝ), (1070917373301/2500000000000 : ℝ), (44655728568439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51358591/250000000 : ℝ)|^2145 ≤ (6253788241187/50000000000000 : ℝ)^1633
        have hw : |(-51358591/250000000 : ℝ)|=(51358591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244444731/10000000000 : ℝ)|^2145 ≤ (1070917373301/2500000000000 : ℝ)^1633
        have hw : |(5244444731/10000000000 : ℝ)|=(5244444731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413144489/10000000000 : ℝ)|^2145 ≤ (44655728568439/100000000000000 : ℝ)^1633
        have hw : |(5413144489/10000000000 : ℝ)|=(5413144489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663200619/1250000000 : ℝ)*x 0 + (-30806493/156250000 : ℝ)*x 1 + (2706572257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663200619/1250000000 : ℝ)^2145 ≤ (21747038419877/50000000000000 : ℝ)^1633 := by
    have hnat : (663200619 : ℕ)^2145*50000000000000^1633 ≤ 21747038419877^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663200619 1250000000 21747038419877 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30806493/156250000 : ℝ)^2145 ≤ (2962548574689/25000000000000 : ℝ)^1633 := by
    have hnat : (30806493 : ℕ)^2145*25000000000000^1633 ≤ 2962548574689^1633*156250000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30806493 156250000 2962548574689 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706572257/5000000000 : ℝ)^2145 ≤ (44655728839339/100000000000000 : ℝ)^1633 := by
    have hnat : (2706572257 : ℕ)^2145*100000000000000^1633 ≤ 44655728839339^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706572257 5000000000 44655728839339 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663200619/1250000000 : ℝ), (-30806493/156250000 : ℝ), (2706572257/5000000000 : ℝ)] ![(21747038419877/50000000000000 : ℝ), (2962548574689/25000000000000 : ℝ), (44655728839339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663200619/1250000000 : ℝ)|^2145 ≤ (21747038419877/50000000000000 : ℝ)^1633
        have hw : |(663200619/1250000000 : ℝ)|=(663200619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30806493/156250000 : ℝ)|^2145 ≤ (2962548574689/25000000000000 : ℝ)^1633
        have hw : |(-30806493/156250000 : ℝ)|=(30806493/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706572257/5000000000 : ℝ)|^2145 ≤ (44655728839339/100000000000000 : ℝ)^1633
        have hw : |(2706572257/5000000000 : ℝ)|=(2706572257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305604613/10000000000 : ℝ)*x 0 + (6766431/12500000 : ℝ)*x 1 + (-1971615623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305604613/10000000000 : ℝ)^2145 ≤ (43494073189391/100000000000000 : ℝ)^1633 := by
    have hnat : (5305604613 : ℕ)^2145*100000000000000^1633 ≤ 43494073189391^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305604613 10000000000 43494073189391 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6766431/12500000 : ℝ)^2145 ≤ (44655731938433/100000000000000 : ℝ)^1633 := by
    have hnat : (6766431 : ℕ)^2145*100000000000000^1633 ≤ 44655731938433^1633*12500000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6766431 12500000 44655731938433 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971615623/10000000000 : ℝ)^2145 ≤ (11850194859291/100000000000000 : ℝ)^1633 := by
    have hnat : (1971615623 : ℕ)^2145*100000000000000^1633 ≤ 11850194859291^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971615623 10000000000 11850194859291 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305604613/10000000000 : ℝ), (6766431/12500000 : ℝ), (-1971615623/10000000000 : ℝ)] ![(43494073189391/100000000000000 : ℝ), (44655731938433/100000000000000 : ℝ), (11850194859291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305604613/10000000000 : ℝ)|^2145 ≤ (43494073189391/100000000000000 : ℝ)^1633
        have hw : |(5305604613/10000000000 : ℝ)|=(5305604613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6766431/12500000 : ℝ)|^2145 ≤ (44655731938433/100000000000000 : ℝ)^1633
        have hw : |(6766431/12500000 : ℝ)|=(6766431/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971615623/10000000000 : ℝ)|^2145 ≤ (11850194859291/100000000000000 : ℝ)^1633
        have hw : |(-1971615623/10000000000 : ℝ)|=(1971615623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s5_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082440583/2500000000 : ℝ)*x 0 + (2254512597/5000000000 : ℝ)*x 1 + (2078632671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082440583/2500000000 : ℝ)^2145 ≤ (65044929349/195312500000 : ℝ)^1633 := by
    have hnat : (1082440583 : ℕ)^2145*195312500000^1633 ≤ 65044929349^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082440583 2500000000 65044929349 195312500000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254512597/5000000000 : ℝ)^2145 ≤ (7025156886479/20000000000000 : ℝ)^1633 := by
    have hnat : (2254512597 : ℕ)^2145*20000000000000^1633 ≤ 7025156886479^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254512597 5000000000 7025156886479 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078632671/5000000000 : ℝ)^2145 ≤ (31571211722897/100000000000000 : ℝ)^1633 := by
    have hnat : (2078632671 : ℕ)^2145*100000000000000^1633 ≤ 31571211722897^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078632671 5000000000 31571211722897 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082440583/2500000000 : ℝ), (2254512597/5000000000 : ℝ), (2078632671/5000000000 : ℝ)] ![(65044929349/195312500000 : ℝ), (7025156886479/20000000000000 : ℝ), (31571211722897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082440583/2500000000 : ℝ)|^2145 ≤ (65044929349/195312500000 : ℝ)^1633
        have hw : |(1082440583/2500000000 : ℝ)|=(1082440583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254512597/5000000000 : ℝ)|^2145 ≤ (7025156886479/20000000000000 : ℝ)^1633
        have hw : |(2254512597/5000000000 : ℝ)|=(2254512597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078632671/5000000000 : ℝ)|^2145 ≤ (31571211722897/100000000000000 : ℝ)^1633
        have hw : |(2078632671/5000000000 : ℝ)|=(2078632671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2213/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2213/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2213/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2213/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2213/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2213/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2213/20000 : ℝ) ^ (4289/1024 : ℝ) ≤ (309359134807567/3125000000000000000 : ℝ) := by
    have hpowers : (2213/20000 : ℝ)^4289 ≤ (309359134807567/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2213 : ℕ)^4289*3125000000000000000^1024 ≤ 309359134807567^1024*20000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2213 20000 309359134807567 3125000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2213/20000 : ℝ)) (X := (309359134807567/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (4289/1024 : ℝ) ≤ (4134292483406573/12500000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^4289 ≤ (4134292483406573/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7379 : ℕ)^4289*12500000000000000000^1024 ≤ 4134292483406573^1024*50000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 4134292483406573 12500000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (4134292483406573/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562809359134807567/1562500000000000000 : ℝ) ≤ (200009453314329/200000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (1562809359134807567/1562500000000000000 : ℝ)^1024 ≤ (200009453314329/200000000000000 : ℝ)^4289 := by
      have hnat : (1562809359134807567 : ℕ)^1024*200000000000000^4289 ≤ 200009453314329^4289*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562809359134807567 1562500000000000000 200009453314329 200000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200009453314329/200000000000000 : ℝ)) (X := (1562809359134807567/1562500000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505371729022636841/12500000000000000000 : ℝ) ≤ (39066507162953/39062500000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (12505371729022636841/12500000000000000000 : ℝ)^1024 ≤ (39066507162953/39062500000000 : ℝ)^4289 := by
      have hnat : (12505371729022636841 : ℕ)^1024*39062500000000^4289 ≤ 39066507162953^4289*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505371729022636841 12500000000000000000 39066507162953 39062500000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39066507162953/39062500000000 : ℝ)) (X := (12505371729022636841/12500000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254134292483406573/6250000000000000000 : ℝ) ≤ (5000789500857743/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (6254134292483406573/6250000000000000000 : ℝ)^1024 ≤ (5000789500857743/5000000000000000 : ℝ)^4289 := by
      have hnat : (6254134292483406573 : ℕ)^1024*5000000000000000^4289 ≤ 5000789500857743^4289*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254134292483406573 6250000000000000000 5000789500857743 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000789500857743/5000000000000000 : ℝ)) (X := (6254134292483406573/6250000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(309359134807567/3125000000000000000 : ℝ) ≤ ((3691950394666151651/3693000000000000000 : ℝ)+2*(276583999759/184650000000000 : ℝ)*(2213/20000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (3691950394666151651/3693000000000000000 : ℝ)+2*(276583999759/184650000000000 : ℝ)*(2213/20000 : ℝ)=(200009453314329/200000000000000 : ℝ) by norm_num, show 1+2*(309359134807567/3125000000000000000 : ℝ)=(1562809359134807567/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4134292483406573/12500000000000000000 : ℝ)+(309359134807567/3125000000000000000 : ℝ) ≤ ((3691950394666151651/3693000000000000000 : ℝ)+(276583999759/184650000000000 : ℝ)*((7379/50000 : ℝ)+(2213/20000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (3691950394666151651/3693000000000000000 : ℝ)+(276583999759/184650000000000 : ℝ)*((7379/50000 : ℝ)+(2213/20000 : ℝ))=(39066507162953/39062500000000 : ℝ) by norm_num, show 1+(4134292483406573/12500000000000000000 : ℝ)+(309359134807567/3125000000000000000 : ℝ)=(12505371729022636841/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4134292483406573/12500000000000000000 : ℝ) ≤ ((3691950394666151651/3693000000000000000 : ℝ)+2*(276583999759/184650000000000 : ℝ)*(7379/50000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (3691950394666151651/3693000000000000000 : ℝ)+2*(276583999759/184650000000000 : ℝ)*(7379/50000 : ℝ)=(5000789500857743/5000000000000000 : ℝ) by norm_num, show 1+2*(4134292483406573/12500000000000000000 : ℝ)=(6254134292483406573/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3691950394666151651/3693000000000000000 : ℝ)*(X 1 0+X 2 0)+(276583999759/184650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (3691950394666151651/3693000000000000000 : ℝ)) (alpha := (276583999759/184650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3691950394666151651/3693000000000000000 : ℝ)*(X 0 1+X 2 1)+(276583999759/184650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (3691950394666151651/3693000000000000000 : ℝ)) (alpha := (276583999759/184650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3691950394666151651/3693000000000000000 : ℝ)*(X 0 2+X 1 2)+(276583999759/184650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (3691950394666151651/3693000000000000000 : ℝ)) (alpha := (276583999759/184650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410866287/2000000000 : ℝ)*X 0 0+(676719807/1250000000 : ℝ)*X 0 1+(2621916857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337328087/2500000000 : ℝ)*X 1 0+(-2140926223/10000000000 : ℝ)*X 1 1+(524383399/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668663943/1250000000 : ℝ)*X 2 0+(131095859/250000000 : ℝ)*X 2 1+(-535231701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082433981/2500000000 : ℝ)*X 0 0+(1038996467/2500000000 : ℝ)*X 0 1+(2255149227/5000000000 : ℝ)*X 0 2+(1082433981/2500000000 : ℝ)*X 1 0+(1038996467/2500000000 : ℝ)*X 1 1+(2255149227/5000000000 : ℝ)*X 1 2+(1082433981/2500000000 : ℝ)*X 2 0+(1038996467/2500000000 : ℝ)*X 2 1+(2255149227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51358591/250000000 : ℝ)*X 0 0+(5244444731/10000000000 : ℝ)*X 0 1+(5413144489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663200619/1250000000 : ℝ)*X 1 0+(-30806493/156250000 : ℝ)*X 1 1+(2706572257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305604613/10000000000 : ℝ)*X 2 0+(6766431/12500000 : ℝ)*X 2 1+(-1971615623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082440583/2500000000 : ℝ)*X 0 0+(2254512597/5000000000 : ℝ)*X 0 1+(2078632671/5000000000 : ℝ)*X 0 2+(1082440583/2500000000 : ℝ)*X 1 0+(2254512597/5000000000 : ℝ)*X 1 1+(2078632671/5000000000 : ℝ)*X 1 2+(1082440583/2500000000 : ℝ)*X 2 0+(2254512597/5000000000 : ℝ)*X 2 1+(2078632671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63432401144946304823709987/15387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191299457/25000000000000 : ℝ)*(base19) + (462315587/100000000000000 : ℝ)*(base23) + (52823871/12500000000000 : ℝ)*(upper2) + (444606047/100000000000000 : ℝ)*(upper3) + (13932289/12500000000000 : ℝ)*(upper4) + (2176844487396437/50000000000000 : ℝ)*(major0) + (2176844487396437/50000000000000 : ℝ)*(major1) + (2176844487396437/50000000000000 : ℝ)*(major2) + (5884993473215269/100000000000000 : ℝ)*(sp0) + (2942498768524141/50000000000000 : ℝ)*(sp1) + (1471249459982631/25000000000000 : ℝ)*(sp2) + (705593120840703/25000000000000 : ℝ)*(sp3) + (4829030841/100000000000000 : ℝ)*(sp4) + (7026565711/100000000000000 : ℝ)*(sp7) + (705594877482131/25000000000000 : ℝ)*(f.failure) + (588499830224611/10000000000000 : ℝ)*(f.sum) + (55557973355207/18465000000000000000000000000 : ℝ)*base65 + (694487659837522513/184650000000000000000000000000000 : ℝ)*base68 + (504236844958522513/184650000000000000000000000000000 : ℝ)*base70 + (2369933219179327487/184650000000000000000000000000000 : ℝ)*base71 + (4490525094757/4616250000000000000000000000 : ℝ)*base74 + (1924332145680772513/184650000000000000000000000000000 : ℝ)*base76 + (181261886998672513/184650000000000000000000000000000 : ℝ)*base78 + (2501840235840772513/184650000000000000000000000000000 : ℝ)*base80 + (28430418684361/9232500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (57518463/2500000000000000000000 : ℝ)*base89 + (57518463/2500000000000000000000 : ℝ)*base91 + (57518463/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134390701623549509250642531/15387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (539681571/25000000000000 : ℝ)*(base19) + (287020439/12500000000000 : ℝ)*(base23) + (3654673/1562500000000 : ℝ)*(upper2) + (178421043/50000000000000 : ℝ)*(upper3) + (208318423/100000000000000 : ℝ)*(upper5) + (2192631411238619/50000000000000 : ℝ)*(major0) + (2192631411238619/50000000000000 : ℝ)*(major1) + (2192631411238619/50000000000000 : ℝ)*(major2) + (38281947347/100000000000000 : ℝ)*(sp1) + (4742687161/10000000000000 : ℝ)*(sp2) + (1185535473467039/20000000000000 : ℝ)*(sp4) + (5927636926661563/100000000000000 : ℝ)*(sp5) + (5927627644300073/100000000000000 : ℝ)*(sp6) + (1421423993247003/50000000000000 : ℝ)*(sp7) + (1421423993247003/50000000000000 : ℝ)*(f.failure) + (1185535473467039/20000000000000 : ℝ)*(f.sum) + (9015804888499/4616250000000000000000000000 : ℝ)*base66 + (905106348841379969/184650000000000000000000000000000 : ℝ)*base67 + (1410135972205679969/184650000000000000000000000000000 : ℝ)*base69 + (635482631871629969/184650000000000000000000000000000 : ℝ)*base71 + (49151337392971/18465000000000000000000000000 : ℝ)*base74 + (995218271505629969/184650000000000000000000000000000 : ℝ)*base75 + (1464006676023420031/184650000000000000000000000000000 : ℝ)*base78 + (776316213525629969/184650000000000000000000000000000 : ℝ)*base79 + (67970567290439/18465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (22901081/5000000000000000000000 : ℝ)*base90 + (22901081/5000000000000000000000 : ℝ)*base92 + (22901081/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1330_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1330_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1330_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1330_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1330_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
