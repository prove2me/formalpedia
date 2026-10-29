-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:25.787186+00:00
-- url     : https://prove2.me/submissions/dd4446ea-cbe0-4f05-aaa6-b47109f2d157

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
theorem support_rectangle_w1337_s6_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024145983/5000000000 : ℝ)*x 0 + (5412983447/10000000000 : ℝ)*x 1 + (2622219567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024145983/5000000000 : ℝ)^4297 ≤ (6236227986561/50000000000000 : ℝ)^3273 := by
    have hnat : (1024145983 : ℕ)^4297*50000000000000^3273 ≤ 6236227986561^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024145983 5000000000 6236227986561 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412983447/10000000000 : ℝ)^4297 ≤ (11168091473537/25000000000000 : ℝ)^3273 := by
    have hnat : (5412983447 : ℕ)^4297*25000000000000^3273 ≤ 11168091473537^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412983447 10000000000 11168091473537 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622219567/5000000000 : ℝ)^4297 ≤ (42855178112669/100000000000000 : ℝ)^3273 := by
    have hnat : (2622219567 : ℕ)^4297*100000000000000^3273 ≤ 42855178112669^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622219567 5000000000 42855178112669 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024145983/5000000000 : ℝ), (5412983447/10000000000 : ℝ), (2622219567/5000000000 : ℝ)] ![(6236227986561/50000000000000 : ℝ), (11168091473537/25000000000000 : ℝ), (42855178112669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024145983/5000000000 : ℝ)|^4297 ≤ (6236227986561/50000000000000 : ℝ)^3273
        have hw : |(-1024145983/5000000000 : ℝ)|=(1024145983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412983447/10000000000 : ℝ)|^4297 ≤ (11168091473537/25000000000000 : ℝ)^3273
        have hw : |(5412983447/10000000000 : ℝ)|=(5412983447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622219567/5000000000 : ℝ)|^4297 ≤ (42855178112669/100000000000000 : ℝ)^3273
        have hw : |(2622219567/5000000000 : ℝ)|=(2622219567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674544619/5000000000 : ℝ)*x 0 + (-533542699/2500000000 : ℝ)*x 1 + (5244439173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674544619/5000000000 : ℝ)^4297 ≤ (43981365566799/100000000000000 : ℝ)^3273 := by
    have hnat : (2674544619 : ℕ)^4297*100000000000000^3273 ≤ 43981365566799^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674544619 5000000000 43981365566799 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533542699/2500000000 : ℝ)^4297 ≤ (13163455879979/100000000000000 : ℝ)^3273 := by
    have hnat : (533542699 : ℕ)^4297*100000000000000^3273 ≤ 13163455879979^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533542699 2500000000 13163455879979 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244439173/10000000000 : ℝ)^4297 ≤ (21427589265533/50000000000000 : ℝ)^3273 := by
    have hnat : (5244439173 : ℕ)^4297*50000000000000^3273 ≤ 21427589265533^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244439173 10000000000 21427589265533 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674544619/5000000000 : ℝ), (-533542699/2500000000 : ℝ), (5244439173/10000000000 : ℝ)] ![(43981365566799/100000000000000 : ℝ), (13163455879979/100000000000000 : ℝ), (21427589265533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674544619/5000000000 : ℝ)|^4297 ≤ (43981365566799/100000000000000 : ℝ)^3273
        have hw : |(2674544619/5000000000 : ℝ)|=(2674544619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533542699/2500000000 : ℝ)|^4297 ≤ (13163455879979/100000000000000 : ℝ)^3273
        have hw : |(-533542699/2500000000 : ℝ)|=(533542699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244439173/10000000000 : ℝ)|^4297 ≤ (21427589265533/50000000000000 : ℝ)^3273
        have hw : |(5244439173/10000000000 : ℝ)|=(5244439173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674544643/5000000000 : ℝ)*x 0 + (2622219539/5000000000 : ℝ)*x 1 + (-2134170859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674544643/5000000000 : ℝ)^4297 ≤ (21990683042471/50000000000000 : ℝ)^3273 := by
    have hnat : (2674544643 : ℕ)^4297*50000000000000^3273 ≤ 21990683042471^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674544643 5000000000 21990683042471 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622219539/5000000000 : ℝ)^4297 ≤ (8571035502379/20000000000000 : ℝ)^3273 := by
    have hnat : (2622219539 : ℕ)^4297*20000000000000^3273 ≤ 8571035502379^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622219539 5000000000 8571035502379 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134170859/10000000000 : ℝ)^4297 ≤ (3290864097533/25000000000000 : ℝ)^3273 := by
    have hnat : (2134170859 : ℕ)^4297*25000000000000^3273 ≤ 3290864097533^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134170859 10000000000 3290864097533 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674544643/5000000000 : ℝ), (2622219539/5000000000 : ℝ), (-2134170859/10000000000 : ℝ)] ![(21990683042471/50000000000000 : ℝ), (8571035502379/20000000000000 : ℝ), (3290864097533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674544643/5000000000 : ℝ)|^4297 ≤ (21990683042471/50000000000000 : ℝ)^3273
        have hw : |(2674544643/5000000000 : ℝ)|=(2674544643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622219539/5000000000 : ℝ)|^4297 ≤ (8571035502379/20000000000000 : ℝ)^3273
        have hw : |(2622219539/5000000000 : ℝ)|=(2622219539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134170859/10000000000 : ℝ)|^4297 ≤ (3290864097533/25000000000000 : ℝ)^3273
        have hw : |(-2134170859/10000000000 : ℝ)|=(2134170859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327926441/10000000000 : ℝ)*x 0 + (519387923/1250000000 : ℝ)*x 1 + (1126866913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327926441/10000000000 : ℝ)^4297 ≤ (16651577033063/50000000000000 : ℝ)^3273 := by
    have hnat : (4327926441 : ℕ)^4297*50000000000000^3273 ≤ 16651577033063^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327926441 10000000000 16651577033063 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519387923/1250000000 : ℝ)^4297 ≤ (15784116456141/50000000000000 : ℝ)^3273 := by
    have hnat : (519387923 : ℕ)^4297*50000000000000^3273 ≤ 15784116456141^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519387923 1250000000 15784116456141 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126866913/2500000000 : ℝ)^4297 ≤ (35128613017459/100000000000000 : ℝ)^3273 := by
    have hnat : (1126866913 : ℕ)^4297*100000000000000^3273 ≤ 35128613017459^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126866913 2500000000 35128613017459 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327926441/10000000000 : ℝ), (519387923/1250000000 : ℝ), (1126866913/2500000000 : ℝ)] ![(16651577033063/50000000000000 : ℝ), (15784116456141/50000000000000 : ℝ), (35128613017459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327926441/10000000000 : ℝ)|^4297 ≤ (16651577033063/50000000000000 : ℝ)^3273
        have hw : |(4327926441/10000000000 : ℝ)|=(4327926441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519387923/1250000000 : ℝ)|^4297 ≤ (15784116456141/50000000000000 : ℝ)^3273
        have hw : |(519387923/1250000000 : ℝ)|=(519387923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126866913/2500000000 : ℝ)|^4297 ≤ (35128613017459/100000000000000 : ℝ)^3273
        have hw : |(1126866913/2500000000 : ℝ)|=(1126866913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204830423/1000000000 : ℝ)*x 0 + (1049008483/2000000000 : ℝ)*x 1 + (5412377037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204830423/1000000000 : ℝ)^4297 ≤ (12472554015089/100000000000000 : ℝ)^3273 := by
    have hnat : (204830423 : ℕ)^4297*100000000000000^3273 ≤ 12472554015089^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204830423 1000000000 12472554015089 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049008483/2000000000 : ℝ)^4297 ≤ (42861650299803/100000000000000 : ℝ)^3273 := by
    have hnat : (1049008483 : ℕ)^4297*100000000000000^3273 ≤ 42861650299803^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049008483 2000000000 42861650299803 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412377037/10000000000 : ℝ)^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273 := by
    have hnat : (5412377037 : ℕ)^4297*4000000000000^3273 ≤ 1786631826703^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412377037 10000000000 1786631826703 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204830423/1000000000 : ℝ), (1049008483/2000000000 : ℝ), (5412377037/10000000000 : ℝ)] ![(12472554015089/100000000000000 : ℝ), (42861650299803/100000000000000 : ℝ), (1786631826703/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204830423/1000000000 : ℝ)|^4297 ≤ (12472554015089/100000000000000 : ℝ)^3273
        have hw : |(-204830423/1000000000 : ℝ)|=(204830423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049008483/2000000000 : ℝ)|^4297 ≤ (42861650299803/100000000000000 : ℝ)^3273
        have hw : |(1049008483/2000000000 : ℝ)|=(1049008483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412377037/10000000000 : ℝ)|^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273
        have hw : |(5412377037/10000000000 : ℝ)|=(5412377037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305701137/10000000000 : ℝ)*x 0 + (-1966232919/10000000000 : ℝ)*x 1 + (5412377037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305701137/10000000000 : ℝ)^4297 ≤ (21756800986019/50000000000000 : ℝ)^3273 := by
    have hnat : (5305701137 : ℕ)^4297*50000000000000^3273 ≤ 21756800986019^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305701137 10000000000 21756800986019 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966232919/10000000000 : ℝ)^4297 ≤ (738787646509/6250000000000 : ℝ)^3273 := by
    have hnat : (1966232919 : ℕ)^4297*6250000000000^3273 ≤ 738787646509^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966232919 10000000000 738787646509 6250000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412377037/10000000000 : ℝ)^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273 := by
    have hnat : (5412377037 : ℕ)^4297*4000000000000^3273 ≤ 1786631826703^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412377037 10000000000 1786631826703 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305701137/10000000000 : ℝ), (-1966232919/10000000000 : ℝ), (5412377037/10000000000 : ℝ)] ![(21756800986019/50000000000000 : ℝ), (738787646509/6250000000000 : ℝ), (1786631826703/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305701137/10000000000 : ℝ)|^4297 ≤ (21756800986019/50000000000000 : ℝ)^3273
        have hw : |(5305701137/10000000000 : ℝ)|=(5305701137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966232919/10000000000 : ℝ)|^4297 ≤ (738787646509/6250000000000 : ℝ)^3273
        have hw : |(-1966232919/10000000000 : ℝ)|=(1966232919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412377037/10000000000 : ℝ)|^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273
        have hw : |(5412377037/10000000000 : ℝ)|=(5412377037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305701137/10000000000 : ℝ)*x 0 + (5412377037/10000000000 : ℝ)*x 1 + (-1966232919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305701137/10000000000 : ℝ)^4297 ≤ (21756800986019/50000000000000 : ℝ)^3273 := by
    have hnat : (5305701137 : ℕ)^4297*50000000000000^3273 ≤ 21756800986019^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305701137 10000000000 21756800986019 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412377037/10000000000 : ℝ)^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273 := by
    have hnat : (5412377037 : ℕ)^4297*4000000000000^3273 ≤ 1786631826703^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412377037 10000000000 1786631826703 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966232919/10000000000 : ℝ)^4297 ≤ (738787646509/6250000000000 : ℝ)^3273 := by
    have hnat : (1966232919 : ℕ)^4297*6250000000000^3273 ≤ 738787646509^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966232919 10000000000 738787646509 6250000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305701137/10000000000 : ℝ), (5412377037/10000000000 : ℝ), (-1966232919/10000000000 : ℝ)] ![(21756800986019/50000000000000 : ℝ), (1786631826703/4000000000000 : ℝ), (738787646509/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305701137/10000000000 : ℝ)|^4297 ≤ (21756800986019/50000000000000 : ℝ)^3273
        have hw : |(5305701137/10000000000 : ℝ)|=(5305701137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412377037/10000000000 : ℝ)|^4297 ≤ (1786631826703/4000000000000 : ℝ)^3273
        have hw : |(5412377037/10000000000 : ℝ)|=(5412377037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966232919/10000000000 : ℝ)|^4297 ≤ (738787646509/6250000000000 : ℝ)^3273
        have hw : |(-1966232919/10000000000 : ℝ)|=(1966232919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s6_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540994011/1250000000 : ℝ)*x 0 + (4506206357/10000000000 : ℝ)*x 1 + (2078185559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540994011/1250000000 : ℝ)^4297 ≤ (8325853290697/25000000000000 : ℝ)^3273 := by
    have hnat : (540994011 : ℕ)^4297*25000000000000^3273 ≤ 8325853290697^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540994011 1250000000 8325853290697 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506206357/10000000000 : ℝ)^4297 ≤ (7023141678457/20000000000000 : ℝ)^3273 := by
    have hnat : (4506206357 : ℕ)^4297*20000000000000^3273 ≤ 7023141678457^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506206357 10000000000 7023141678457 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078185559/5000000000 : ℝ)^4297 ≤ (31580878431051/100000000000000 : ℝ)^3273 := by
    have hnat : (2078185559 : ℕ)^4297*100000000000000^3273 ≤ 31580878431051^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078185559 5000000000 31580878431051 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540994011/1250000000 : ℝ), (4506206357/10000000000 : ℝ), (2078185559/5000000000 : ℝ)] ![(8325853290697/25000000000000 : ℝ), (7023141678457/20000000000000 : ℝ), (31580878431051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540994011/1250000000 : ℝ)|^4297 ≤ (8325853290697/25000000000000 : ℝ)^3273
        have hw : |(540994011/1250000000 : ℝ)|=(540994011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506206357/10000000000 : ℝ)|^4297 ≤ (7023141678457/20000000000000 : ℝ)^3273
        have hw : |(4506206357/10000000000 : ℝ)|=(4506206357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078185559/5000000000 : ℝ)|^4297 ≤ (31580878431051/100000000000000 : ℝ)^3273
        have hw : |(2078185559/5000000000 : ℝ)|=(2078185559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11129/100000 : ℝ) ^ (537/128 : ℝ) ≤ (9990461142281469/100000000000000000000 : ℝ) := by
    have hpowers : (11129/100000 : ℝ)^537 ≤ (9990461142281469/100000000000000000000 : ℝ)^128 := by
      have hnat : (11129 : ℕ)^537*100000000000000000000^128 ≤ 9990461142281469^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11129 100000 9990461142281469 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11129/100000 : ℝ)) (X := (9990461142281469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (537/128 : ℝ) ≤ (16114490979388963/50000000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^537 ≤ (16114490979388963/50000000000000000000 : ℝ)^128 := by
      have hnat : (14713 : ℕ)^537*50000000000000000000^128 ≤ 16114490979388963^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 16114490979388963 50000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (16114490979388963/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009990461142281469/50000000000000000000 : ℝ) ≤ (10000476231558201/10000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50009990461142281469/50000000000000000000 : ℝ)^128 ≤ (10000476231558201/10000000000000000 : ℝ)^537 := by
      have hnat : (50009990461142281469 : ℕ)^128*10000000000000000^537 ≤ 10000476231558201^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009990461142281469 50000000000000000000 10000476231558201 10000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000476231558201/10000000000000000 : ℝ)) (X := (50009990461142281469/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008443888620211879/20000000000000000000 : ℝ) ≤ (5000503093115819/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (20008443888620211879/20000000000000000000 : ℝ)^128 ≤ (5000503093115819/5000000000000000 : ℝ)^537 := by
      have hnat : (20008443888620211879 : ℕ)^128*5000000000000000^537 ≤ 5000503093115819^537*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008443888620211879 20000000000000000000 5000503093115819 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000503093115819/5000000000000000 : ℝ)) (X := (20008443888620211879/20000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016114490979388963/25000000000000000000 : ℝ) ≤ (400061445636203/400000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (25016114490979388963/25000000000000000000 : ℝ)^128 ≤ (400061445636203/400000000000000 : ℝ)^537 := by
      have hnat : (25016114490979388963 : ℕ)^128*400000000000000^537 ≤ 400061445636203^537*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016114490979388963 25000000000000000000 400061445636203 400000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400061445636203/400000000000000 : ℝ)) (X := (25016114490979388963/25000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9990461142281469/100000000000000000000 : ℝ) ≤ ((2559279363055945117/2560000000000000000 : ℝ)+2*(75707810491/51200000000000 : ℝ)*(11129/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (2559279363055945117/2560000000000000000 : ℝ)+2*(75707810491/51200000000000 : ℝ)*(11129/100000 : ℝ)=(10000476231558201/10000000000000000 : ℝ) by norm_num, show 1+2*(9990461142281469/100000000000000000000 : ℝ)=(50009990461142281469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16114490979388963/50000000000000000000 : ℝ)+(9990461142281469/100000000000000000000 : ℝ) ≤ ((2559279363055945117/2560000000000000000 : ℝ)+(75707810491/51200000000000 : ℝ)*((14713/100000 : ℝ)+(11129/100000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (2559279363055945117/2560000000000000000 : ℝ)+(75707810491/51200000000000 : ℝ)*((14713/100000 : ℝ)+(11129/100000 : ℝ))=(5000503093115819/5000000000000000 : ℝ) by norm_num, show 1+(16114490979388963/50000000000000000000 : ℝ)+(9990461142281469/100000000000000000000 : ℝ)=(20008443888620211879/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16114490979388963/50000000000000000000 : ℝ) ≤ ((2559279363055945117/2560000000000000000 : ℝ)+2*(75707810491/51200000000000 : ℝ)*(14713/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (2559279363055945117/2560000000000000000 : ℝ)+2*(75707810491/51200000000000 : ℝ)*(14713/100000 : ℝ)=(400061445636203/400000000000000 : ℝ) by norm_num, show 1+2*(16114490979388963/50000000000000000000 : ℝ)=(25016114490979388963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2559279363055945117/2560000000000000000 : ℝ)*(X 1 0+X 2 0)+(75707810491/51200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2559279363055945117/2560000000000000000 : ℝ)) (alpha := (75707810491/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2559279363055945117/2560000000000000000 : ℝ)*(X 0 1+X 2 1)+(75707810491/51200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2559279363055945117/2560000000000000000 : ℝ)) (alpha := (75707810491/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2559279363055945117/2560000000000000000 : ℝ)*(X 0 2+X 1 2)+(75707810491/51200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (2559279363055945117/2560000000000000000 : ℝ)) (alpha := (75707810491/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1024145983/5000000000 : ℝ)*X 0 0+(5412983447/10000000000 : ℝ)*X 0 1+(2622219567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674544619/5000000000 : ℝ)*X 1 0+(-533542699/2500000000 : ℝ)*X 1 1+(5244439173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674544643/5000000000 : ℝ)*X 2 0+(2622219539/5000000000 : ℝ)*X 2 1+(-2134170859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327926441/10000000000 : ℝ)*X 0 0+(519387923/1250000000 : ℝ)*X 0 1+(1126866913/2500000000 : ℝ)*X 0 2+(4327926441/10000000000 : ℝ)*X 1 0+(519387923/1250000000 : ℝ)*X 1 1+(1126866913/2500000000 : ℝ)*X 1 2+(4327926441/10000000000 : ℝ)*X 2 0+(519387923/1250000000 : ℝ)*X 2 1+(1126866913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204830423/1000000000 : ℝ)*X 0 0+(1049008483/2000000000 : ℝ)*X 0 1+(5412377037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305701137/10000000000 : ℝ)*X 1 0+(-1966232919/10000000000 : ℝ)*X 1 1+(5412377037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305701137/10000000000 : ℝ)*X 2 0+(5412377037/10000000000 : ℝ)*X 2 1+(-1966232919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540994011/1250000000 : ℝ)*X 0 0+(4506206357/10000000000 : ℝ)*X 0 1+(2078185559/5000000000 : ℝ)*X 0 2+(540994011/1250000000 : ℝ)*X 1 0+(4506206357/10000000000 : ℝ)*X 1 1+(2078185559/5000000000 : ℝ)*X 1 2+(540994011/1250000000 : ℝ)*X 2 0+(4506206357/10000000000 : ℝ)*X 2 1+(2078185559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7900885200386693749647/2560000000000000000000000000 : ℝ) := by norm_num
    linear_combination (488728881/100000000000000 : ℝ)*(base19) + (506654237/100000000000000 : ℝ)*(base23) + (2375727/12500000000000 : ℝ)*(lower2) + (11621317/12500000000000 : ℝ)*(upper3) + (28747/25000000000000 : ℝ)*(lower4) + (4385581341402559/100000000000000 : ℝ)*(major0) + (4385581341402559/100000000000000 : ℝ)*(major1) + (4385581341402559/100000000000000 : ℝ)*(major2) + (1483292514483189/25000000000000 : ℝ)*(sp0) + (5933179250571469/100000000000000 : ℝ)*(sp1) + (5933179232646113/100000000000000 : ℝ)*(sp2) + (2837976659471489/100000000000000 : ℝ)*(sp3) + (4840683797/50000000000000 : ℝ)*(sp4) + (1545289291/25000000000000 : ℝ)*(sp7) + (2837982840628653/100000000000000 : ℝ)*(f.failure) + (118663594786007/2000000000000 : ℝ)*(f.sum) + (1294063255931/2560000000000000000000000000 : ℝ)*base66 + (98569482334804403/256000000000000000000000000000000 : ℝ)*base67 + (2483005095841195597/256000000000000000000000000000000 : ℝ)*base70 + (171497701537195597/256000000000000000000000000000000 : ℝ)*base72 + (454025486469/2560000000000000000000000000 : ℝ)*base73 + (2337428866721195597/256000000000000000000000000000000 : ℝ)*base76 + (1287678056286804403/256000000000000000000000000000000 : ℝ)*base77 + (1798815403102804403/256000000000000000000000000000000 : ℝ)*base79 + (5562617362811/2560000000000000000000000000 : ℝ)*base82 + (42805039/10000000000000000000000 : ℝ)*base90 + (42805039/10000000000000000000000 : ℝ)*base92 + (42805039/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (370925941271026503683563401/32000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2021418327/100000000000000 : ℝ)*(base19) + (1098100147/50000000000000 : ℝ)*(base23) + (235699377/100000000000000 : ℝ)*(upper3) + (3965573/5000000000000 : ℝ)*(lower4) + (23782957/10000000000000 : ℝ)*(upper5) + (1104317042021483/25000000000000 : ℝ)*(major0) + (1104317042021483/25000000000000 : ℝ)*(major1) + (1104317042021483/25000000000000 : ℝ)*(major2) + (20592471519/50000000000000 : ℝ)*(sp1) + (4427851371/10000000000000 : ℝ)*(sp2) + (2988024017528231/50000000000000 : ℝ)*(sp4) + (5976004828695097/100000000000000 : ℝ)*(sp5) + (2988000780171229/50000000000000 : ℝ)*(sp6) + (571697582946841/20000000000000 : ℝ)*(sp7) + (571697582946841/20000000000000 : ℝ)*(f.failure) + (2988024017528231/50000000000000 : ℝ)*(f.sum) + (2499940121047/640000000000000000000000000 : ℝ)*base66 + (459573131130598511/64000000000000000000000000000000 : ℝ)*base67 + (173948979514598511/64000000000000000000000000000000 : ℝ)*base69 + (343301549818598511/64000000000000000000000000000000 : ℝ)*base71 + (763357090007/640000000000000000000000000 : ℝ)*base74 + (45254447098598511/64000000000000000000000000000000 : ℝ)*base75 + (273091279546598511/64000000000000000000000000000000 : ℝ)*base77 + (721444452986598511/64000000000000000000000000000000 : ℝ)*base79 + (2831001563433/640000000000000000000000000 : ℝ)*base81 + (16291283/2000000000000000000000 : ℝ)*base90 + (16291283/2000000000000000000000 : ℝ)*base92 + (16291283/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_s7_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048298457/10000000000 : ℝ)*x 0 + (3383073/6250000 : ℝ)*x 1 + (5244501607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048298457/10000000000 : ℝ)^4297 ≤ (12472507864033/100000000000000 : ℝ)^3273 := by
    have hnat : (2048298457 : ℕ)^4297*100000000000000^3273 ≤ 12472507864033^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048298457 10000000000 12472507864033 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3383073/6250000 : ℝ)^4297 ≤ (11167910946863/25000000000000 : ℝ)^3273 := by
    have hnat : (3383073 : ℕ)^4297*25000000000000^3273 ≤ 11167910946863^3273*6250000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383073 6250000 11167910946863 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244501607/10000000000 : ℝ)^4297 ≤ (42855848331729/100000000000000 : ℝ)^3273 := by
    have hnat : (5244501607 : ℕ)^4297*100000000000000^3273 ≤ 42855848331729^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244501607 10000000000 42855848331729 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048298457/10000000000 : ℝ), (3383073/6250000 : ℝ), (5244501607/10000000000 : ℝ)] ![(12472507864033/100000000000000 : ℝ), (11167910946863/25000000000000 : ℝ), (42855848331729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048298457/10000000000 : ℝ)|^4297 ≤ (12472507864033/100000000000000 : ℝ)^3273
        have hw : |(-2048298457/10000000000 : ℝ)|=(2048298457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3383073/6250000 : ℝ)|^4297 ≤ (11167910946863/25000000000000 : ℝ)^3273
        have hw : |(3383073/6250000 : ℝ)|=(3383073/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244501607/10000000000 : ℝ)|^4297 ≤ (42855848331729/100000000000000 : ℝ)^3273
        have hw : |(5244501607/10000000000 : ℝ)|=(5244501607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349072579/10000000000 : ℝ)*x 0 + (-1067055151/5000000000 : ℝ)*x 1 + (5244501597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349072579/10000000000 : ℝ)^4297 ≤ (43981185738957/100000000000000 : ℝ)^3273 := by
    have hnat : (5349072579 : ℕ)^4297*100000000000000^3273 ≤ 43981185738957^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349072579 10000000000 43981185738957 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067055151/5000000000 : ℝ)^4297 ≤ (3290741505419/25000000000000 : ℝ)^3273 := by
    have hnat : (1067055151 : ℕ)^4297*25000000000000^3273 ≤ 3290741505419^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067055151 5000000000 3290741505419 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244501597/10000000000 : ℝ)^4297 ≤ (669622628507/1562500000000 : ℝ)^3273 := by
    have hnat : (5244501597 : ℕ)^4297*1562500000000^3273 ≤ 669622628507^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244501597 10000000000 669622628507 1562500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349072579/10000000000 : ℝ), (-1067055151/5000000000 : ℝ), (5244501597/10000000000 : ℝ)] ![(43981185738957/100000000000000 : ℝ), (3290741505419/25000000000000 : ℝ), (669622628507/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349072579/10000000000 : ℝ)|^4297 ≤ (43981185738957/100000000000000 : ℝ)^3273
        have hw : |(5349072579/10000000000 : ℝ)|=(5349072579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067055151/5000000000 : ℝ)|^4297 ≤ (3290741505419/25000000000000 : ℝ)^3273
        have hw : |(-1067055151/5000000000 : ℝ)|=(1067055151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244501597/10000000000 : ℝ)|^4297 ≤ (669622628507/1562500000000 : ℝ)^3273
        have hw : |(5244501597/10000000000 : ℝ)|=(5244501597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534907259/1000000000 : ℝ)*x 0 + (5244501591/10000000000 : ℝ)*x 1 + (-426822059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534907259/1000000000 : ℝ)^4297 ≤ (21990592928849/50000000000000 : ℝ)^3273 := by
    have hnat : (534907259 : ℕ)^4297*50000000000000^3273 ≤ 21990592928849^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534907259 1000000000 21990592928849 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244501591/10000000000 : ℝ)^4297 ≤ (42855848160079/100000000000000 : ℝ)^3273 := by
    have hnat : (5244501591 : ℕ)^4297*100000000000000^3273 ≤ 42855848160079^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244501591 10000000000 42855848160079 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426822059/2000000000 : ℝ)^4297 ≤ (205671343203/1562500000000 : ℝ)^3273 := by
    have hnat : (426822059 : ℕ)^4297*1562500000000^3273 ≤ 205671343203^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426822059 2000000000 205671343203 1562500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534907259/1000000000 : ℝ), (5244501591/10000000000 : ℝ), (-426822059/2000000000 : ℝ)] ![(21990592928849/50000000000000 : ℝ), (42855848160079/100000000000000 : ℝ), (205671343203/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534907259/1000000000 : ℝ)|^4297 ≤ (21990592928849/50000000000000 : ℝ)^3273
        have hw : |(534907259/1000000000 : ℝ)|=(534907259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244501591/10000000000 : ℝ)|^4297 ≤ (42855848160079/100000000000000 : ℝ)^3273
        have hw : |(5244501591/10000000000 : ℝ)|=(5244501591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426822059/2000000000 : ℝ)|^4297 ≤ (205671343203/1562500000000 : ℝ)^3273
        have hw : |(-426822059/2000000000 : ℝ)|=(426822059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327931073/10000000000 : ℝ)*x 0 + (6492559/15625000 : ℝ)*x 1 + (2253666039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327931073/10000000000 : ℝ)^4297 ≤ (33303200860481/100000000000000 : ℝ)^3273 := by
    have hnat : (4327931073 : ℕ)^4297*100000000000000^3273 ≤ 33303200860481^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327931073 10000000000 33303200860481 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6492559/15625000 : ℝ)^4297 ≤ (15784786621071/50000000000000 : ℝ)^3273 := by
    have hnat : (6492559 : ℕ)^4297*50000000000000^3273 ≤ 15784786621071^3273*15625000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6492559 15625000 15784786621071 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253666039/5000000000 : ℝ)^4297 ≤ (17563612935849/50000000000000 : ℝ)^3273 := by
    have hnat : (2253666039 : ℕ)^4297*50000000000000^3273 ≤ 17563612935849^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253666039 5000000000 17563612935849 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327931073/10000000000 : ℝ), (6492559/15625000 : ℝ), (2253666039/5000000000 : ℝ)] ![(33303200860481/100000000000000 : ℝ), (15784786621071/50000000000000 : ℝ), (17563612935849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327931073/10000000000 : ℝ)|^4297 ≤ (33303200860481/100000000000000 : ℝ)^3273
        have hw : |(4327931073/10000000000 : ℝ)|=(4327931073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6492559/15625000 : ℝ)|^4297 ≤ (15784786621071/50000000000000 : ℝ)^3273
        have hw : |(6492559/15625000 : ℝ)|=(6492559/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253666039/5000000000 : ℝ)|^4297 ≤ (17563612935849/50000000000000 : ℝ)^3273
        have hw : |(2253666039/5000000000 : ℝ)|=(2253666039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6400971/31250000 : ℝ)*x 0 + (5245103911/10000000000 : ℝ)*x 1 + (2706155677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6400971/31250000 : ℝ)^4297 ≤ (6236302949051/50000000000000 : ℝ)^3273 := by
    have hnat : (6400971 : ℕ)^4297*50000000000000^3273 ≤ 6236302949051^3273*31250000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6400971 31250000 6236302949051 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245103911/10000000000 : ℝ)^4297 ≤ (21431155030597/50000000000000 : ℝ)^3273 := by
    have hnat : (5245103911 : ℕ)^4297*50000000000000^3273 ≤ 21431155030597^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245103911 10000000000 21431155030597 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706155677/5000000000 : ℝ)^4297 ≤ (44665084030549/100000000000000 : ℝ)^3273 := by
    have hnat : (2706155677 : ℕ)^4297*100000000000000^3273 ≤ 44665084030549^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706155677 5000000000 44665084030549 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6400971/31250000 : ℝ), (5245103911/10000000000 : ℝ), (2706155677/5000000000 : ℝ)] ![(6236302949051/50000000000000 : ℝ), (21431155030597/50000000000000 : ℝ), (44665084030549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6400971/31250000 : ℝ)|^4297 ≤ (6236302949051/50000000000000 : ℝ)^3273
        have hw : |(-6400971/31250000 : ℝ)|=(6400971/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245103911/10000000000 : ℝ)|^4297 ≤ (21431155030597/50000000000000 : ℝ)^3273
        have hw : |(5245103911/10000000000 : ℝ)|=(5245103911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706155677/5000000000 : ℝ)|^4297 ≤ (44665084030549/100000000000000 : ℝ)^3273
        have hw : |(2706155677/5000000000 : ℝ)|=(2706155677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305717291/10000000000 : ℝ)*x 0 + (-1966300891/10000000000 : ℝ)*x 1 + (5412311467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305717291/10000000000 : ℝ)^4297 ≤ (43513775904997/100000000000000 : ℝ)^3273 := by
    have hnat : (5305717291 : ℕ)^4297*100000000000000^3273 ≤ 43513775904997^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305717291 10000000000 43513775904997 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966300891/10000000000 : ℝ)^4297 ≤ (1182113882767/10000000000000 : ℝ)^3273 := by
    have hnat : (1966300891 : ℕ)^4297*10000000000000^3273 ≤ 1182113882767^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966300891 10000000000 1182113882767 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412311467/10000000000 : ℝ)^4297 ≤ (8933017050967/20000000000000 : ℝ)^3273 := by
    have hnat : (5412311467 : ℕ)^4297*20000000000000^3273 ≤ 8933017050967^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412311467 10000000000 8933017050967 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305717291/10000000000 : ℝ), (-1966300891/10000000000 : ℝ), (5412311467/10000000000 : ℝ)] ![(43513775904997/100000000000000 : ℝ), (1182113882767/10000000000000 : ℝ), (8933017050967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305717291/10000000000 : ℝ)|^4297 ≤ (43513775904997/100000000000000 : ℝ)^3273
        have hw : |(5305717291/10000000000 : ℝ)|=(5305717291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966300891/10000000000 : ℝ)|^4297 ≤ (1182113882767/10000000000000 : ℝ)^3273
        have hw : |(-1966300891/10000000000 : ℝ)|=(1966300891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412311467/10000000000 : ℝ)|^4297 ≤ (8933017050967/20000000000000 : ℝ)^3273
        have hw : |(5412311467/10000000000 : ℝ)|=(5412311467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061143537/2000000000 : ℝ)*x 0 + (5412311349/10000000000 : ℝ)*x 1 + (-491575129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061143537/2000000000 : ℝ)^4297 ≤ (43513780147267/100000000000000 : ℝ)^3273 := by
    have hnat : (1061143537 : ℕ)^4297*100000000000000^3273 ≤ 43513780147267^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061143537 2000000000 43513780147267 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412311349/10000000000 : ℝ)^4297 ≤ (44665083976377/100000000000000 : ℝ)^3273 := by
    have hnat : (5412311349 : ℕ)^4297*100000000000000^3273 ≤ 44665083976377^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412311349 10000000000 44665083976377 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491575129/2500000000 : ℝ)^4297 ≤ (5910567933943/50000000000000 : ℝ)^3273 := by
    have hnat : (491575129 : ℕ)^4297*50000000000000^3273 ≤ 5910567933943^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491575129 2500000000 5910567933943 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061143537/2000000000 : ℝ), (5412311349/10000000000 : ℝ), (-491575129/2500000000 : ℝ)] ![(43513780147267/100000000000000 : ℝ), (44665083976377/100000000000000 : ℝ), (5910567933943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061143537/2000000000 : ℝ)|^4297 ≤ (43513780147267/100000000000000 : ℝ)^3273
        have hw : |(1061143537/2000000000 : ℝ)|=(1061143537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412311349/10000000000 : ℝ)|^4297 ≤ (44665083976377/100000000000000 : ℝ)^3273
        have hw : |(5412311349/10000000000 : ℝ)|=(5412311349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491575129/2500000000 : ℝ)|^4297 ≤ (5910567933943/50000000000000 : ℝ)^3273
        have hw : |(-491575129/2500000000 : ℝ)|=(491575129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s7_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327956751/10000000000 : ℝ)*x 0 + (563259091/1250000000 : ℝ)*x 1 + (831300689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327956751/10000000000 : ℝ)^4297 ≤ (6660692054081/20000000000000 : ℝ)^3273 := by
    have hnat : (4327956751 : ℕ)^4297*20000000000000^3273 ≤ 6660692054081^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327956751 10000000000 6660692054081 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563259091/1250000000 : ℝ)^4297 ≤ (17557170633351/50000000000000 : ℝ)^3273 := by
    have hnat : (563259091 : ℕ)^4297*50000000000000^3273 ≤ 17557170633351^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563259091 1250000000 17557170633351 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831300689/2000000000 : ℝ)^4297 ≤ (493471850767/1562500000000 : ℝ)^3273 := by
    have hnat : (831300689 : ℕ)^4297*1562500000000^3273 ≤ 493471850767^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831300689 2000000000 493471850767 1562500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327956751/10000000000 : ℝ), (563259091/1250000000 : ℝ), (831300689/2000000000 : ℝ)] ![(6660692054081/20000000000000 : ℝ), (17557170633351/50000000000000 : ℝ), (493471850767/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327956751/10000000000 : ℝ)|^4297 ≤ (6660692054081/20000000000000 : ℝ)^3273
        have hw : |(4327956751/10000000000 : ℝ)|=(4327956751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563259091/1250000000 : ℝ)|^4297 ≤ (17557170633351/50000000000000 : ℝ)^3273
        have hw : |(563259091/1250000000 : ℝ)|=(563259091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831300689/2000000000 : ℝ)|^4297 ≤ (493471850767/1562500000000 : ℝ)^3273
        have hw : |(831300689/2000000000 : ℝ)|=(831300689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11137/100000 : ℝ) ^ (537/128 : ℝ) ≤ (10020624691573613/100000000000000000000 : ℝ) := by
    have hpowers : (11137/100000 : ℝ)^537 ≤ (10020624691573613/100000000000000000000 : ℝ)^128 := by
      have hnat : (11137 : ℕ)^537*100000000000000000000^128 ≤ 10020624691573613^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11137 100000 10020624691573613 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11137/100000 : ℝ)) (X := (10020624691573613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (537/128 : ℝ) ≤ (257244214310361/800000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^537 ≤ (257244214310361/800000000000000000 : ℝ)^128 := by
      have hnat : (2941 : ℕ)^537*800000000000000000^128 ≤ 257244214310361^128*20000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 257244214310361 800000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (257244214310361/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010020624691573613/50000000000000000000 : ℝ) ≤ (5000238834651719/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50010020624691573613/50000000000000000000 : ℝ)^128 ≤ (5000238834651719/5000000000000000 : ℝ)^537 := by
      have hnat : (50010020624691573613 : ℕ)^128*5000000000000000^537 ≤ 5000238834651719^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010020624691573613 50000000000000000000 5000238834651719 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000238834651719/5000000000000000 : ℝ)) (X := (50010020624691573613/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021088075740184369/50000000000000000000 : ℝ) ≤ (1000100515465861/1000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50021088075740184369/50000000000000000000 : ℝ)^128 ≤ (1000100515465861/1000000000000000 : ℝ)^537 := by
      have hnat : (50021088075740184369 : ℕ)^128*1000000000000000^537 ≤ 1000100515465861^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021088075740184369 50000000000000000000 1000100515465861 1000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000100515465861/1000000000000000 : ℝ)) (X := (50021088075740184369/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (400257244214310361/400000000000000000 : ℝ) ≤ (5000766320006891/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (400257244214310361/400000000000000000 : ℝ)^128 ≤ (5000766320006891/5000000000000000 : ℝ)^537 := by
      have hnat : (400257244214310361 : ℕ)^128*5000000000000000^537 ≤ 5000766320006891^537*400000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400257244214310361 400000000000000000 5000766320006891 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000766320006891/5000000000000000 : ℝ)) (X := (400257244214310361/400000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10020624691573613/100000000000000000000 : ℝ) ≤ ((4458744389409195707/4460000000000000000 : ℝ)+2*(131871338793/89200000000000 : ℝ)*(11137/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (4458744389409195707/4460000000000000000 : ℝ)+2*(131871338793/89200000000000 : ℝ)*(11137/100000 : ℝ)=(5000238834651719/5000000000000000 : ℝ) by norm_num, show 1+2*(10020624691573613/100000000000000000000 : ℝ)=(50010020624691573613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(257244214310361/800000000000000000 : ℝ)+(10020624691573613/100000000000000000000 : ℝ) ≤ ((4458744389409195707/4460000000000000000 : ℝ)+(131871338793/89200000000000 : ℝ)*((2941/20000 : ℝ)+(11137/100000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (4458744389409195707/4460000000000000000 : ℝ)+(131871338793/89200000000000 : ℝ)*((2941/20000 : ℝ)+(11137/100000 : ℝ))=(1000100515465861/1000000000000000 : ℝ) by norm_num, show 1+(257244214310361/800000000000000000 : ℝ)+(10020624691573613/100000000000000000000 : ℝ)=(50021088075740184369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(257244214310361/800000000000000000 : ℝ) ≤ ((4458744389409195707/4460000000000000000 : ℝ)+2*(131871338793/89200000000000 : ℝ)*(2941/20000 : ℝ))^(537/128 : ℝ) := by
    rw [show (4458744389409195707/4460000000000000000 : ℝ)+2*(131871338793/89200000000000 : ℝ)*(2941/20000 : ℝ)=(5000766320006891/5000000000000000 : ℝ) by norm_num, show 1+2*(257244214310361/800000000000000000 : ℝ)=(400257244214310361/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4458744389409195707/4460000000000000000 : ℝ)*(X 1 0+X 2 0)+(131871338793/89200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (4458744389409195707/4460000000000000000 : ℝ)) (alpha := (131871338793/89200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4458744389409195707/4460000000000000000 : ℝ)*(X 0 1+X 2 1)+(131871338793/89200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (4458744389409195707/4460000000000000000 : ℝ)) (alpha := (131871338793/89200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4458744389409195707/4460000000000000000 : ℝ)*(X 0 2+X 1 2)+(131871338793/89200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (4458744389409195707/4460000000000000000 : ℝ)) (alpha := (131871338793/89200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2048298457/10000000000 : ℝ)*X 0 0+(3383073/6250000 : ℝ)*X 0 1+(5244501607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349072579/10000000000 : ℝ)*X 1 0+(-1067055151/5000000000 : ℝ)*X 1 1+(5244501597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534907259/1000000000 : ℝ)*X 2 0+(5244501591/10000000000 : ℝ)*X 2 1+(-426822059/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327931073/10000000000 : ℝ)*X 0 0+(6492559/15625000 : ℝ)*X 0 1+(2253666039/5000000000 : ℝ)*X 0 2+(4327931073/10000000000 : ℝ)*X 1 0+(6492559/15625000 : ℝ)*X 1 1+(2253666039/5000000000 : ℝ)*X 1 2+(4327931073/10000000000 : ℝ)*X 2 0+(6492559/15625000 : ℝ)*X 2 1+(2253666039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6400971/31250000 : ℝ)*X 0 0+(5245103911/10000000000 : ℝ)*X 0 1+(2706155677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305717291/10000000000 : ℝ)*X 1 0+(-1966300891/10000000000 : ℝ)*X 1 1+(5412311467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061143537/2000000000 : ℝ)*X 2 0+(5412311349/10000000000 : ℝ)*X 2 1+(-491575129/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327956751/10000000000 : ℝ)*X 0 0+(563259091/1250000000 : ℝ)*X 0 1+(831300689/2000000000 : ℝ)*X 0 2+(4327956751/10000000000 : ℝ)*X 1 0+(563259091/1250000000 : ℝ)*X 1 1+(831300689/2000000000 : ℝ)*X 1 2+(4327956751/10000000000 : ℝ)*X 2 0+(563259091/1250000000 : ℝ)*X 2 1+(831300689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171848396165473033718579937/27875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229089993/20000000000000 : ℝ)*(base19) + (535322023/50000000000000 : ℝ)*(base23) + (46545757/100000000000000 : ℝ)*(lower2) + (18843451/12500000000000 : ℝ)*(upper3) + (48548799/50000000000000 : ℝ)*(upper5) + (548620273239901/12500000000000 : ℝ)*(major0) + (548620273239901/12500000000000 : ℝ)*(major1) + (548620273239901/12500000000000 : ℝ)*(major2) + (742216300178683/12500000000000 : ℝ)*(sp0) + (5937752379379351/100000000000000 : ℝ)*(sp1) + (5937752454185269/100000000000000 : ℝ)*(sp2) + (142007936102853/5000000000000 : ℝ)*(sp3) + (23123399851/100000000000000 : ℝ)*(sp4) + (29798633/250000000000 : ℝ)*(sp7) + (2840170641510261/100000000000000 : ℝ)*(f.failure) + (1484438381207329/25000000000000 : ℝ)*(f.sum) + (2248052891803/557500000000000000000000000 : ℝ)*base65 + (343804745344205007/55750000000000000000000000000000 : ℝ)*base67 + (50968174248455007/55750000000000000000000000000000 : ℝ)*base69 + (148057176843205007/55750000000000000000000000000000 : ℝ)*base71 + (547393882701/69687500000000000000000000 : ℝ)*base73 + (580929533789705007/55750000000000000000000000000000 : ℝ)*base75 + (609847780027455007/55750000000000000000000000000000 : ℝ)*base77 + (673747153965705007/55750000000000000000000000000000 : ℝ)*base79 + (2555222803389/1115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15372743/10000000000000000000000 : ℝ)*base90 + (15372743/10000000000000000000000 : ℝ)*base92 + (15372743/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (283058421426372907019124759/44600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457443169/100000000000000 : ℝ)*(base19) + (578334973/50000000000000 : ℝ)*(base23) + (121670373/100000000000000 : ℝ)*(lower1) + (155770989/100000000000000 : ℝ)*(upper3) + (29710969/50000000000000 : ℝ)*(lower4) + (88169951/50000000000000 : ℝ)*(upper5) + (884125291141721/20000000000000 : ℝ)*(major0) + (884125291141721/20000000000000 : ℝ)*(major1) + (884125291141721/20000000000000 : ℝ)*(major2) + (17514224457/100000000000000 : ℝ)*(sp2) + (149514789529759/2500000000000 : ℝ)*(sp4) + (747573890468399/12500000000000 : ℝ)*(sp5) + (5980572910295957/100000000000000 : ℝ)*(sp6) + (178791319917091/6250000000000 : ℝ)*(sp7) + (178791319917091/6250000000000 : ℝ)*(f.failure) + (149514789529759/2500000000000 : ℝ)*(f.sum) + (4682318390401/892000000000000000000000000 : ℝ)*base65 + (702630541721841747/89200000000000000000000000000000 : ℝ)*base67 + (269930490787441747/89200000000000000000000000000000 : ℝ)*base69 + (5024972140358158253/89200000000000000000000000000000 : ℝ)*base72 + (152069744479/892000000000000000000000000 : ℝ)*base74 + (1068720956793358253/89200000000000000000000000000000 : ℝ)*base76 + (471698101414241747/89200000000000000000000000000000 : ℝ)*base77 + (201680744217841747/89200000000000000000000000000000 : ℝ)*base79 + (6647648577397/892000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4742033/625000000000000000000 : ℝ)*base90 + (4742033/625000000000000000000 : ℝ)*base92 + (4742033/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_box_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-470161819/2500000000 : ℝ)*x 0 + (8624239/16000000 : ℝ)*x 1 + (2695074599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470161819/2500000000 : ℝ)^4297 ≤ (1114974929569/10000000000000 : ℝ)^3273 := by
    have hnat : (470161819 : ℕ)^4297*10000000000000^3273 ≤ 1114974929569^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470161819 2500000000 1114974929569 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8624239/16000000 : ℝ)^4297 ≤ (4442512630621/10000000000000 : ℝ)^3273 := by
    have hnat : (8624239 : ℕ)^4297*10000000000000^3273 ≤ 4442512630621^3273*16000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8624239 16000000 4442512630621 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695074599/5000000000 : ℝ)^4297 ≤ (22212562195491/50000000000000 : ℝ)^3273 := by
    have hnat : (2695074599 : ℕ)^4297*50000000000000^3273 ≤ 22212562195491^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695074599 5000000000 22212562195491 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470161819/2500000000 : ℝ), (8624239/16000000 : ℝ), (2695074599/5000000000 : ℝ)] ![(1114974929569/10000000000000 : ℝ), (4442512630621/10000000000000 : ℝ), (22212562195491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470161819/2500000000 : ℝ)|^4297 ≤ (1114974929569/10000000000000 : ℝ)^3273
        have hw : |(-470161819/2500000000 : ℝ)|=(470161819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8624239/16000000 : ℝ)|^4297 ≤ (4442512630621/10000000000000 : ℝ)^3273
        have hw : |(8624239/16000000 : ℝ)|=(8624239/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695074599/5000000000 : ℝ)|^4297 ≤ (22212562195491/50000000000000 : ℝ)^3273
        have hw : |(2695074599/5000000000 : ℝ)|=(2695074599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285094711/10000000000 : ℝ)*x 0 + (-2024551163/10000000000 : ℝ)*x 1 + (1347537329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285094711/10000000000 : ℝ)^4297 ≤ (2164593199221/5000000000000 : ℝ)^3273 := by
    have hnat : (5285094711 : ℕ)^4297*5000000000000^3273 ≤ 2164593199221^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285094711 10000000000 2164593199221 5000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024551163/10000000000 : ℝ)^4297 ≤ (6141505165029/50000000000000 : ℝ)^3273 := by
    have hnat : (2024551163 : ℕ)^4297*50000000000000^3273 ≤ 6141505165029^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024551163 10000000000 6141505165029 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347537329/2500000000 : ℝ)^4297 ≤ (44425125667801/100000000000000 : ℝ)^3273 := by
    have hnat : (1347537329 : ℕ)^4297*100000000000000^3273 ≤ 44425125667801^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347537329 2500000000 44425125667801 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285094711/10000000000 : ℝ), (-2024551163/10000000000 : ℝ), (1347537329/2500000000 : ℝ)] ![(2164593199221/5000000000000 : ℝ), (6141505165029/50000000000000 : ℝ), (44425125667801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285094711/10000000000 : ℝ)|^4297 ≤ (2164593199221/5000000000000 : ℝ)^3273
        have hw : |(5285094711/10000000000 : ℝ)|=(5285094711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024551163/10000000000 : ℝ)|^4297 ≤ (6141505165029/50000000000000 : ℝ)^3273
        have hw : |(-2024551163/10000000000 : ℝ)|=(2024551163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347537329/2500000000 : ℝ)|^4297 ≤ (44425125667801/100000000000000 : ℝ)^3273
        have hw : |(1347537329/2500000000 : ℝ)|=(1347537329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528509443/1000000000 : ℝ)*x 0 + (5390149509/10000000000 : ℝ)*x 1 + (-25306891/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528509443/1000000000 : ℝ)^4297 ≤ (21645930481263/50000000000000 : ℝ)^3273 := by
    have hnat : (528509443 : ℕ)^4297*50000000000000^3273 ≤ 21645930481263^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528509443 1000000000 21645930481263 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390149509/10000000000 : ℝ)^4297 ≤ (44425127756157/100000000000000 : ℝ)^3273 := by
    have hnat : (5390149509 : ℕ)^4297*100000000000000^3273 ≤ 44425127756157^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390149509 10000000000 44425127756157 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25306891/125000000 : ℝ)^4297 ≤ (12283011261983/100000000000000 : ℝ)^3273 := by
    have hnat : (25306891 : ℕ)^4297*100000000000000^3273 ≤ 12283011261983^3273*125000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25306891 125000000 12283011261983 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528509443/1000000000 : ℝ), (5390149509/10000000000 : ℝ), (-25306891/125000000 : ℝ)] ![(21645930481263/50000000000000 : ℝ), (44425127756157/100000000000000 : ℝ), (12283011261983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528509443/1000000000 : ℝ)|^4297 ≤ (21645930481263/50000000000000 : ℝ)^3273
        have hw : |(528509443/1000000000 : ℝ)|=(528509443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390149509/10000000000 : ℝ)|^4297 ≤ (44425127756157/100000000000000 : ℝ)^3273
        have hw : |(5390149509/10000000000 : ℝ)|=(5390149509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25306891/125000000 : ℝ)|^4297 ≤ (12283011261983/100000000000000 : ℝ)^3273
        have hw : |(-25306891/125000000 : ℝ)|=(25306891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4476239231/10000000000 : ℝ)*x 0 + (4257677257/10000000000 : ℝ)*x 1 + (85153557/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476239231/10000000000 : ℝ)^4297 ≤ (8702360017701/25000000000000 : ℝ)^3273 := by
    have hnat : (4476239231 : ℕ)^4297*25000000000000^3273 ≤ 8702360017701^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476239231 10000000000 8702360017701 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4257677257/10000000000 : ℝ)^4297 ≤ (32595276977723/100000000000000 : ℝ)^3273 := by
    have hnat : (4257677257 : ℕ)^4297*100000000000000^3273 ≤ 32595276977723^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257677257 10000000000 32595276977723 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85153557/200000000 : ℝ)^4297 ≤ (32595282937857/100000000000000 : ℝ)^3273 := by
    have hnat : (85153557 : ℕ)^4297*100000000000000^3273 ≤ 32595282937857^3273*200000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85153557 200000000 32595282937857 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476239231/10000000000 : ℝ), (4257677257/10000000000 : ℝ), (85153557/200000000 : ℝ)] ![(8702360017701/25000000000000 : ℝ), (32595276977723/100000000000000 : ℝ), (32595282937857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476239231/10000000000 : ℝ)|^4297 ≤ (8702360017701/25000000000000 : ℝ)^3273
        have hw : |(4476239231/10000000000 : ℝ)|=(4476239231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4257677257/10000000000 : ℝ)|^4297 ≤ (32595276977723/100000000000000 : ℝ)^3273
        have hw : |(4257677257/10000000000 : ℝ)|=(4257677257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85153557/200000000 : ℝ)|^4297 ≤ (32595282937857/100000000000000 : ℝ)^3273
        have hw : |(85153557/200000000 : ℝ)|=(85153557/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-554676759/2500000000 : ℝ)*x 0 + (5264814629/10000000000 : ℝ)*x 1 + (263240687/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554676759/2500000000 : ℝ)^4297 ≤ (13852206345289/100000000000000 : ℝ)^3273 := by
    have hnat : (554676759 : ℕ)^4297*100000000000000^3273 ≤ 13852206345289^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554676759 2500000000 13852206345289 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264814629/10000000000 : ℝ)^4297 ≤ (43073901591343/100000000000000 : ℝ)^3273 := by
    have hnat : (5264814629 : ℕ)^4297*100000000000000^3273 ≤ 43073901591343^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264814629 10000000000 43073901591343 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263240687/500000000 : ℝ)^4297 ≤ (43073892042467/100000000000000 : ℝ)^3273 := by
    have hnat : (263240687 : ℕ)^4297*100000000000000^3273 ≤ 43073892042467^3273*500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263240687 500000000 43073892042467 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554676759/2500000000 : ℝ), (5264814629/10000000000 : ℝ), (263240687/500000000 : ℝ)] ![(13852206345289/100000000000000 : ℝ), (43073901591343/100000000000000 : ℝ), (43073892042467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554676759/2500000000 : ℝ)|^4297 ≤ (13852206345289/100000000000000 : ℝ)^3273
        have hw : |(-554676759/2500000000 : ℝ)|=(554676759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264814629/10000000000 : ℝ)|^4297 ≤ (43073901591343/100000000000000 : ℝ)^3273
        have hw : |(5264814629/10000000000 : ℝ)|=(5264814629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263240687/500000000 : ℝ)|^4297 ≤ (43073892042467/100000000000000 : ℝ)^3273
        have hw : |(263240687/500000000 : ℝ)|=(263240687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373147267/10000000000 : ℝ)*x 0 + (-2074808777/10000000000 : ℝ)*x 1 + (1316203323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373147267/10000000000 : ℝ)^4297 ≤ (1382538933941/3125000000000 : ℝ)^3273 := by
    have hnat : (5373147267 : ℕ)^4297*3125000000000^3273 ≤ 1382538933941^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373147267 10000000000 1382538933941 3125000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074808777/10000000000 : ℝ)^4297 ≤ (2536973373291/20000000000000 : ℝ)^3273 := by
    have hnat : (2074808777 : ℕ)^4297*20000000000000^3273 ≤ 2536973373291^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074808777 10000000000 2536973373291 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316203323/2500000000 : ℝ)^4297 ≤ (10768471807609/25000000000000 : ℝ)^3273 := by
    have hnat : (1316203323 : ℕ)^4297*25000000000000^3273 ≤ 10768471807609^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316203323 2500000000 10768471807609 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373147267/10000000000 : ℝ), (-2074808777/10000000000 : ℝ), (1316203323/2500000000 : ℝ)] ![(1382538933941/3125000000000 : ℝ), (2536973373291/20000000000000 : ℝ), (10768471807609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373147267/10000000000 : ℝ)|^4297 ≤ (1382538933941/3125000000000 : ℝ)^3273
        have hw : |(5373147267/10000000000 : ℝ)|=(5373147267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074808777/10000000000 : ℝ)|^4297 ≤ (2536973373291/20000000000000 : ℝ)^3273
        have hw : |(-2074808777/10000000000 : ℝ)|=(2074808777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316203323/2500000000 : ℝ)|^4297 ≤ (10768471807609/25000000000000 : ℝ)^3273
        have hw : |(1316203323/2500000000 : ℝ)|=(1316203323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373146461/10000000000 : ℝ)*x 0 + (329050861/625000000 : ℝ)*x 1 + (-414961843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373146461/10000000000 : ℝ)^4297 ≤ (44241237173407/100000000000000 : ℝ)^3273 := by
    have hnat : (5373146461 : ℕ)^4297*100000000000000^3273 ≤ 44241237173407^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373146461 10000000000 44241237173407 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329050861/625000000 : ℝ)^4297 ≤ (43073892429149/100000000000000 : ℝ)^3273 := by
    have hnat : (329050861 : ℕ)^4297*100000000000000^3273 ≤ 43073892429149^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329050861 625000000 43073892429149 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414961843/2000000000 : ℝ)^4297 ≤ (1268487038207/10000000000000 : ℝ)^3273 := by
    have hnat : (414961843 : ℕ)^4297*10000000000000^3273 ≤ 1268487038207^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414961843 2000000000 1268487038207 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373146461/10000000000 : ℝ), (329050861/625000000 : ℝ), (-414961843/2000000000 : ℝ)] ![(44241237173407/100000000000000 : ℝ), (43073892429149/100000000000000 : ℝ), (1268487038207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373146461/10000000000 : ℝ)|^4297 ≤ (44241237173407/100000000000000 : ℝ)^3273
        have hw : |(5373146461/10000000000 : ℝ)|=(5373146461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329050861/625000000 : ℝ)|^4297 ≤ (43073892429149/100000000000000 : ℝ)^3273
        have hw : |(329050861/625000000 : ℝ)|=(329050861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414961843/2000000000 : ℝ)|^4297 ≤ (1268487038207/10000000000000 : ℝ)^3273
        have hw : |(-414961843/2000000000 : ℝ)|=(414961843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417870419/1000000000 : ℝ)*x 0 + (550798837/1250000000 : ℝ)*x 1 + (4406391913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417870419/1000000000 : ℝ)^4297 ≤ (6360769245563/20000000000000 : ℝ)^3273 := by
    have hnat : (417870419 : ℕ)^4297*20000000000000^3273 ≤ 6360769245563^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417870419 1000000000 6360769245563 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550798837/1250000000 : ℝ)^4297 ≤ (34098070694039/100000000000000 : ℝ)^3273 := by
    have hnat : (550798837 : ℕ)^4297*100000000000000^3273 ≤ 34098070694039^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550798837 1250000000 34098070694039 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406391913/10000000000 : ℝ)^4297 ≤ (1363923322319/4000000000000 : ℝ)^3273 := by
    have hnat : (4406391913 : ℕ)^4297*4000000000000^3273 ≤ 1363923322319^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406391913 10000000000 1363923322319 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417870419/1000000000 : ℝ), (550798837/1250000000 : ℝ), (4406391913/10000000000 : ℝ)] ![(6360769245563/20000000000000 : ℝ), (34098070694039/100000000000000 : ℝ), (1363923322319/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417870419/1000000000 : ℝ)|^4297 ≤ (6360769245563/20000000000000 : ℝ)^3273
        have hw : |(417870419/1000000000 : ℝ)|=(417870419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550798837/1250000000 : ℝ)|^4297 ≤ (34098070694039/100000000000000 : ℝ)^3273
        have hw : |(550798837/1250000000 : ℝ)|=(550798837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406391913/10000000000 : ℝ)|^4297 ≤ (1363923322319/4000000000000 : ℝ)^3273
        have hw : |(4406391913/10000000000 : ℝ)|=(4406391913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_8 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073864377/5000000000 : ℝ)*x 0 + (2589276511/5000000000 : ℝ)*x 1 + (1351042777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073864377/5000000000 : ℝ)^4297 ≤ (6636676351031/50000000000000 : ℝ)^3273 := by
    have hnat : (1073864377 : ℕ)^4297*50000000000000^3273 ≤ 6636676351031^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073864377 5000000000 6636676351031 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589276511/5000000000 : ℝ)^4297 ≤ (42149737155567/100000000000000 : ℝ)^3273 := by
    have hnat : (2589276511 : ℕ)^4297*100000000000000^3273 ≤ 42149737155567^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589276511 5000000000 42149737155567 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351042777/2500000000 : ℝ)^4297 ≤ (11144227533447/25000000000000 : ℝ)^3273 := by
    have hnat : (1351042777 : ℕ)^4297*25000000000000^3273 ≤ 11144227533447^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351042777 2500000000 11144227533447 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073864377/5000000000 : ℝ), (2589276511/5000000000 : ℝ), (1351042777/2500000000 : ℝ)] ![(6636676351031/50000000000000 : ℝ), (42149737155567/100000000000000 : ℝ), (11144227533447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073864377/5000000000 : ℝ)|^4297 ≤ (6636676351031/50000000000000 : ℝ)^3273
        have hw : |(-1073864377/5000000000 : ℝ)|=(1073864377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589276511/5000000000 : ℝ)|^4297 ≤ (42149737155567/100000000000000 : ℝ)^3273
        have hw : |(2589276511/5000000000 : ℝ)|=(2589276511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351042777/2500000000 : ℝ)|^4297 ≤ (11144227533447/25000000000000 : ℝ)^3273
        have hw : |(1351042777/2500000000 : ℝ)|=(1351042777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_9 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275238647/10000000000 : ℝ)*x 0 + (-1009397961/5000000000 : ℝ)*x 1 + (5404170971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275238647/10000000000 : ℝ)^4297 ≤ (10796475529059/25000000000000 : ℝ)^3273 := by
    have hnat : (5275238647 : ℕ)^4297*25000000000000^3273 ≤ 10796475529059^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275238647 10000000000 10796475529059 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009397961/5000000000 : ℝ)^4297 ≤ (3059297304437/25000000000000 : ℝ)^3273 := by
    have hnat : (1009397961 : ℕ)^4297*25000000000000^3273 ≤ 3059297304437^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009397961 5000000000 3059297304437 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404170971/10000000000 : ℝ)^4297 ≤ (22288454325087/50000000000000 : ℝ)^3273 := by
    have hnat : (5404170971 : ℕ)^4297*50000000000000^3273 ≤ 22288454325087^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404170971 10000000000 22288454325087 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275238647/10000000000 : ℝ), (-1009397961/5000000000 : ℝ), (5404170971/10000000000 : ℝ)] ![(10796475529059/25000000000000 : ℝ), (3059297304437/25000000000000 : ℝ), (22288454325087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275238647/10000000000 : ℝ)|^4297 ≤ (10796475529059/25000000000000 : ℝ)^3273
        have hw : |(5275238647/10000000000 : ℝ)|=(5275238647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009397961/5000000000 : ℝ)|^4297 ≤ (3059297304437/25000000000000 : ℝ)^3273
        have hw : |(-1009397961/5000000000 : ℝ)|=(1009397961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404170971/10000000000 : ℝ)|^4297 ≤ (22288454325087/50000000000000 : ℝ)^3273
        have hw : |(5404170971/10000000000 : ℝ)|=(5404170971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_10 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637619159/5000000000 : ℝ)*x 0 + (5404171337/10000000000 : ℝ)*x 1 + (-504698967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637619159/5000000000 : ℝ)^4297 ≤ (43185898580213/100000000000000 : ℝ)^3273 := by
    have hnat : (2637619159 : ℕ)^4297*100000000000000^3273 ≤ 43185898580213^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637619159 5000000000 43185898580213 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404171337/10000000000 : ℝ)^4297 ≤ (696514259589/1562500000000 : ℝ)^3273 := by
    have hnat : (5404171337 : ℕ)^4297*1562500000000^3273 ≤ 696514259589^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404171337 10000000000 696514259589 1562500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504698967/2500000000 : ℝ)^4297 ≤ (3059297197003/25000000000000 : ℝ)^3273 := by
    have hnat : (504698967 : ℕ)^4297*25000000000000^3273 ≤ 3059297197003^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504698967 2500000000 3059297197003 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637619159/5000000000 : ℝ), (5404171337/10000000000 : ℝ), (-504698967/2500000000 : ℝ)] ![(43185898580213/100000000000000 : ℝ), (696514259589/1562500000000 : ℝ), (3059297197003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637619159/5000000000 : ℝ)|^4297 ≤ (43185898580213/100000000000000 : ℝ)^3273
        have hw : |(2637619159/5000000000 : ℝ)|=(2637619159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404171337/10000000000 : ℝ)|^4297 ≤ (696514259589/1562500000000 : ℝ)^3273
        have hw : |(5404171337/10000000000 : ℝ)|=(5404171337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-504698967/2500000000 : ℝ)|^4297 ≤ (3059297197003/25000000000000 : ℝ)^3273
        have hw : |(-504698967/2500000000 : ℝ)|=(504698967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_11 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2254483463/5000000000 : ℝ)*x 0 + (1060256517/2500000000 : ℝ)*x 1 + (848205277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254483463/5000000000 : ℝ)^4297 ≤ (35143953935059/100000000000000 : ℝ)^3273 := by
    have hnat : (2254483463 : ℕ)^4297*100000000000000^3273 ≤ 35143953935059^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254483463 5000000000 35143953935059 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060256517/2500000000 : ℝ)^4297 ≤ (16214010716601/50000000000000 : ℝ)^3273 := by
    have hnat : (1060256517 : ℕ)^4297*50000000000000^3273 ≤ 16214010716601^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060256517 2500000000 16214010716601 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848205277/2000000000 : ℝ)^4297 ≤ (32428024615407/100000000000000 : ℝ)^3273 := by
    have hnat : (848205277 : ℕ)^4297*100000000000000^3273 ≤ 32428024615407^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848205277 2000000000 32428024615407 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254483463/5000000000 : ℝ), (1060256517/2500000000 : ℝ), (848205277/2000000000 : ℝ)] ![(35143953935059/100000000000000 : ℝ), (16214010716601/50000000000000 : ℝ), (32428024615407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254483463/5000000000 : ℝ)|^4297 ≤ (35143953935059/100000000000000 : ℝ)^3273
        have hw : |(2254483463/5000000000 : ℝ)|=(2254483463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060256517/2500000000 : ℝ)|^4297 ≤ (16214010716601/50000000000000 : ℝ)^3273
        have hw : |(1060256517/2500000000 : ℝ)|=(1060256517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848205277/2000000000 : ℝ)|^4297 ≤ (32428024615407/100000000000000 : ℝ)^3273
        have hw : |(848205277/2000000000 : ℝ)|=(848205277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_12 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487993361/2500000000 : ℝ)*x 0 + (5474193903/10000000000 : ℝ)*x 1 + (525374823/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487993361/2500000000 : ℝ)^4297 ≤ (2927046223259/25000000000000 : ℝ)^3273 := by
    have hnat : (487993361 : ℕ)^4297*25000000000000^3273 ≤ 2927046223259^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487993361 2500000000 2927046223259 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474193903/10000000000 : ℝ)^4297 ≤ (5667092520183/12500000000000 : ℝ)^3273 := by
    have hnat : (5474193903 : ℕ)^4297*12500000000000^3273 ≤ 5667092520183^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474193903 10000000000 5667092520183 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525374823/1000000000 : ℝ)^4297 ≤ (42955074926813/100000000000000 : ℝ)^3273 := by
    have hnat : (525374823 : ℕ)^4297*100000000000000^3273 ≤ 42955074926813^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525374823 1000000000 42955074926813 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487993361/2500000000 : ℝ), (5474193903/10000000000 : ℝ), (525374823/1000000000 : ℝ)] ![(2927046223259/25000000000000 : ℝ), (5667092520183/12500000000000 : ℝ), (42955074926813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487993361/2500000000 : ℝ)|^4297 ≤ (2927046223259/25000000000000 : ℝ)^3273
        have hw : |(-487993361/2500000000 : ℝ)|=(487993361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474193903/10000000000 : ℝ)|^4297 ≤ (5667092520183/12500000000000 : ℝ)^3273
        have hw : |(5474193903/10000000000 : ℝ)|=(5474193903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525374823/1000000000 : ℝ)|^4297 ≤ (42955074926813/100000000000000 : ℝ)^3273
        have hw : |(525374823/1000000000 : ℝ)|=(525374823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_13 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336307339/625000000 : ℝ)*x 0 + (-2079142407/10000000000 : ℝ)*x 1 + (1313437153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336307339/625000000 : ℝ)^4297 ≤ (22162629390369/50000000000000 : ℝ)^3273 := by
    have hnat : (336307339 : ℕ)^4297*50000000000000^3273 ≤ 22162629390369^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336307339 625000000 22162629390369 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079142407/10000000000 : ℝ)^4297 ≤ (12719662185523/100000000000000 : ℝ)^3273 := by
    have hnat : (2079142407 : ℕ)^4297*100000000000000^3273 ≤ 12719662185523^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079142407 10000000000 12719662185523 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313437153/2500000000 : ℝ)^4297 ≤ (42955079027229/100000000000000 : ℝ)^3273 := by
    have hnat : (1313437153 : ℕ)^4297*100000000000000^3273 ≤ 42955079027229^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313437153 2500000000 42955079027229 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336307339/625000000 : ℝ), (-2079142407/10000000000 : ℝ), (1313437153/2500000000 : ℝ)] ![(22162629390369/50000000000000 : ℝ), (12719662185523/100000000000000 : ℝ), (42955079027229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336307339/625000000 : ℝ)|^4297 ≤ (22162629390369/50000000000000 : ℝ)^3273
        have hw : |(336307339/625000000 : ℝ)|=(336307339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079142407/10000000000 : ℝ)|^4297 ≤ (12719662185523/100000000000000 : ℝ)^3273
        have hw : |(-2079142407/10000000000 : ℝ)|=(2079142407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313437153/2500000000 : ℝ)|^4297 ≤ (42955079027229/100000000000000 : ℝ)^3273
        have hw : |(1313437153/2500000000 : ℝ)|=(1313437153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_14 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690459129/5000000000 : ℝ)*x 0 + (5253747971/10000000000 : ℝ)*x 1 + (-2079142139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690459129/5000000000 : ℝ)^4297 ≤ (22162633900097/50000000000000 : ℝ)^3273 := by
    have hnat : (2690459129 : ℕ)^4297*50000000000000^3273 ≤ 22162633900097^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690459129 5000000000 22162633900097 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253747971/10000000000 : ℝ)^4297 ≤ (167793250573/390625000000 : ℝ)^3273 := by
    have hnat : (5253747971 : ℕ)^4297*390625000000^3273 ≤ 167793250573^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253747971 10000000000 167793250573 390625000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079142139/10000000000 : ℝ)^4297 ≤ (12719660033011/100000000000000 : ℝ)^3273 := by
    have hnat : (2079142139 : ℕ)^4297*100000000000000^3273 ≤ 12719660033011^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079142139 10000000000 12719660033011 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690459129/5000000000 : ℝ), (5253747971/10000000000 : ℝ), (-2079142139/10000000000 : ℝ)] ![(22162633900097/50000000000000 : ℝ), (167793250573/390625000000 : ℝ), (12719660033011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690459129/5000000000 : ℝ)|^4297 ≤ (22162633900097/50000000000000 : ℝ)^3273
        have hw : |(2690459129/5000000000 : ℝ)|=(2690459129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253747971/10000000000 : ℝ)|^4297 ≤ (167793250573/390625000000 : ℝ)^3273
        have hw : |(5253747971/10000000000 : ℝ)|=(5253747971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079142139/10000000000 : ℝ)|^4297 ≤ (12719660033011/100000000000000 : ℝ)^3273
        have hw : |(-2079142139/10000000000 : ℝ)|=(2079142139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_box_15 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037997411/2500000000 : ℝ)*x 0 + (4419509263/10000000000 : ℝ)*x 1 + (883901919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037997411/2500000000 : ℝ)^4297 ≤ (3942147349187/12500000000000 : ℝ)^3273 := by
    have hnat : (1037997411 : ℕ)^4297*12500000000000^3273 ≤ 3942147349187^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037997411 2500000000 3942147349187 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419509263/10000000000 : ℝ)^4297 ≤ (34231408906093/100000000000000 : ℝ)^3273 := by
    have hnat : (4419509263 : ℕ)^4297*100000000000000^3273 ≤ 34231408906093^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419509263 10000000000 34231408906093 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883901919/2000000000 : ℝ)^4297 ≤ (17115706141069/50000000000000 : ℝ)^3273 := by
    have hnat : (883901919 : ℕ)^4297*50000000000000^3273 ≤ 17115706141069^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883901919 2000000000 17115706141069 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037997411/2500000000 : ℝ), (4419509263/10000000000 : ℝ), (883901919/2000000000 : ℝ)] ![(3942147349187/12500000000000 : ℝ), (34231408906093/100000000000000 : ℝ), (17115706141069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037997411/2500000000 : ℝ)|^4297 ≤ (3942147349187/12500000000000 : ℝ)^3273
        have hw : |(1037997411/2500000000 : ℝ)|=(1037997411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419509263/10000000000 : ℝ)|^4297 ≤ (34231408906093/100000000000000 : ℝ)^3273
        have hw : |(4419509263/10000000000 : ℝ)|=(4419509263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(883901919/2000000000 : ℝ)|^4297 ≤ (17115706141069/50000000000000 : ℝ)^3273
        have hw : |(883901919/2000000000 : ℝ)|=(883901919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62853/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58931/100000 : ℝ) ∧ (3197/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84333/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5569/50000 : ℝ) ^ (537/128 : ℝ) ≤ (5012200003289413/50000000000000000000 : ℝ) := by
    have hpowers : (5569/50000 : ℝ)^537 ≤ (5012200003289413/50000000000000000000 : ℝ)^128 := by
      have hnat : (5569 : ℕ)^537*50000000000000000000^128 ≤ 5012200003289413^128*50000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5569 50000 5012200003289413 50000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5569/50000 : ℝ)) (X := (5012200003289413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14703/100000 : ℝ) ^ (537/128 : ℝ) ≤ (16068591468327557/50000000000000000000 : ℝ) := by
    have hpowers : (14703/100000 : ℝ)^537 ≤ (16068591468327557/50000000000000000000 : ℝ)^128 := by
      have hnat : (14703 : ℕ)^537*50000000000000000000^128 ≤ 16068591468327557^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14703 100000 16068591468327557 50000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14703/100000 : ℝ)) (X := (16068591468327557/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005012200003289413/25000000000000000000 : ℝ) ≤ (5000238924626869/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (25005012200003289413/25000000000000000000 : ℝ)^128 ≤ (5000238924626869/5000000000000000 : ℝ)^537 := by
      have hnat : (25005012200003289413 : ℕ)^128*5000000000000000^537 ≤ 5000238924626869^537*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005012200003289413 25000000000000000000 5000238924626869 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000238924626869/5000000000000000 : ℝ)) (X := (25005012200003289413/25000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002108079147161697/5000000000000000000 : ℝ) ≤ (10001004807512603/10000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (5002108079147161697/5000000000000000000 : ℝ)^128 ≤ (10001004807512603/10000000000000000 : ℝ)^537 := by
      have hnat : (5002108079147161697 : ℕ)^128*10000000000000000^537 ≤ 10001004807512603^537*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002108079147161697 5000000000000000000 10001004807512603 10000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001004807512603/10000000000000000 : ℝ)) (X := (5002108079147161697/5000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016068591468327557/25000000000000000000 : ℝ) ≤ (2500382941442867/2500000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (25016068591468327557/25000000000000000000 : ℝ)^128 ≤ (2500382941442867/2500000000000000 : ℝ)^537 := by
      have hnat : (25016068591468327557 : ℕ)^128*2500000000000000^537 ≤ 2500382941442867^537*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016068591468327557 25000000000000000000 2500382941442867 2500000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500382941442867/2500000000000000 : ℝ)) (X := (25016068591468327557/25000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5012200003289413/50000000000000000000 : ℝ) ≤ ((3563996501041509923/3565000000000000000 : ℝ)+2*(105391651773/71300000000000 : ℝ)*(5569/50000 : ℝ))^(537/128 : ℝ) := by
    rw [show (3563996501041509923/3565000000000000000 : ℝ)+2*(105391651773/71300000000000 : ℝ)*(5569/50000 : ℝ)=(5000238924626869/5000000000000000 : ℝ) by norm_num, show 1+2*(5012200003289413/50000000000000000000 : ℝ)=(25005012200003289413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16068591468327557/50000000000000000000 : ℝ)+(5012200003289413/50000000000000000000 : ℝ) ≤ ((3563996501041509923/3565000000000000000 : ℝ)+(105391651773/71300000000000 : ℝ)*((14703/100000 : ℝ)+(5569/50000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (3563996501041509923/3565000000000000000 : ℝ)+(105391651773/71300000000000 : ℝ)*((14703/100000 : ℝ)+(5569/50000 : ℝ))=(10001004807512603/10000000000000000 : ℝ) by norm_num, show 1+(16068591468327557/50000000000000000000 : ℝ)+(5012200003289413/50000000000000000000 : ℝ)=(5002108079147161697/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16068591468327557/50000000000000000000 : ℝ) ≤ ((3563996501041509923/3565000000000000000 : ℝ)+2*(105391651773/71300000000000 : ℝ)*(14703/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (3563996501041509923/3565000000000000000 : ℝ)+2*(105391651773/71300000000000 : ℝ)*(14703/100000 : ℝ)=(2500382941442867/2500000000000000 : ℝ) by norm_num, show 1+2*(16068591468327557/50000000000000000000 : ℝ)=(25016068591468327557/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3563996501041509923/3565000000000000000 : ℝ)*(X 1 0+X 2 0)+(105391651773/71300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (3563996501041509923/3565000000000000000 : ℝ)) (alpha := (105391651773/71300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3563996501041509923/3565000000000000000 : ℝ)*(X 0 1+X 2 1)+(105391651773/71300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (3563996501041509923/3565000000000000000 : ℝ)) (alpha := (105391651773/71300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3563996501041509923/3565000000000000000 : ℝ)*(X 0 2+X 1 2)+(105391651773/71300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (3563996501041509923/3565000000000000000 : ℝ)) (alpha := (105391651773/71300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-470161819/2500000000 : ℝ)*X 0 0+(8624239/16000000 : ℝ)*X 0 1+(2695074599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285094711/10000000000 : ℝ)*X 1 0+(-2024551163/10000000000 : ℝ)*X 1 1+(1347537329/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528509443/1000000000 : ℝ)*X 2 0+(5390149509/10000000000 : ℝ)*X 2 1+(-25306891/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4476239231/10000000000 : ℝ)*X 0 0+(4257677257/10000000000 : ℝ)*X 0 1+(85153557/200000000 : ℝ)*X 0 2+(4476239231/10000000000 : ℝ)*X 1 0+(4257677257/10000000000 : ℝ)*X 1 1+(85153557/200000000 : ℝ)*X 1 2+(4476239231/10000000000 : ℝ)*X 2 0+(4257677257/10000000000 : ℝ)*X 2 1+(85153557/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-554676759/2500000000 : ℝ)*X 0 0+(5264814629/10000000000 : ℝ)*X 0 1+(263240687/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373147267/10000000000 : ℝ)*X 1 0+(-2074808777/10000000000 : ℝ)*X 1 1+(1316203323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373146461/10000000000 : ℝ)*X 2 0+(329050861/625000000 : ℝ)*X 2 1+(-414961843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417870419/1000000000 : ℝ)*X 0 0+(550798837/1250000000 : ℝ)*X 0 1+(4406391913/10000000000 : ℝ)*X 0 2+(417870419/1000000000 : ℝ)*X 1 0+(550798837/1250000000 : ℝ)*X 1 1+(4406391913/10000000000 : ℝ)*X 1 2+(417870419/1000000000 : ℝ)*X 2 0+(550798837/1250000000 : ℝ)*X 2 1+(4406391913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1073864377/5000000000 : ℝ)*X 0 0+(2589276511/5000000000 : ℝ)*X 0 1+(1351042777/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275238647/10000000000 : ℝ)*X 1 0+(-1009397961/5000000000 : ℝ)*X 1 1+(5404170971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637619159/5000000000 : ℝ)*X 2 0+(5404171337/10000000000 : ℝ)*X 2 1+(-504698967/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2254483463/5000000000 : ℝ)*X 0 0+(1060256517/2500000000 : ℝ)*X 0 1+(848205277/2000000000 : ℝ)*X 0 2+(2254483463/5000000000 : ℝ)*X 1 0+(1060256517/2500000000 : ℝ)*X 1 1+(848205277/2000000000 : ℝ)*X 1 2+(2254483463/5000000000 : ℝ)*X 2 0+(1060256517/2500000000 : ℝ)*X 2 1+(848205277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-487993361/2500000000 : ℝ)*X 0 0+(5474193903/10000000000 : ℝ)*X 0 1+(525374823/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((336307339/625000000 : ℝ)*X 1 0+(-2079142407/10000000000 : ℝ)*X 1 1+(1313437153/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690459129/5000000000 : ℝ)*X 2 0+(5253747971/10000000000 : ℝ)*X 2 1+(-2079142139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1037997411/2500000000 : ℝ)*X 0 0+(4419509263/10000000000 : ℝ)*X 0 1+(883901919/2000000000 : ℝ)*X 0 2+(1037997411/2500000000 : ℝ)*X 1 0+(4419509263/10000000000 : ℝ)*X 1 1+(883901919/2000000000 : ℝ)*X 1 2+(1037997411/2500000000 : ℝ)*X 2 0+(4419509263/10000000000 : ℝ)*X 2 1+(883901919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62853/100000 : ℝ) ≤ (-14003961523640474901459038655231/22281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (464257/20000000000000 : ℝ)*(lower1) + (80559813/100000000000000 : ℝ)*(lower3) + (73357179/20000000000000 : ℝ)*(lower4) + (364376711472501/12500000000000 : ℝ)*(major0) + (364376711472501/12500000000000 : ℝ)*(major1) + (364376711472501/12500000000000 : ℝ)*(major2) + (16383749579/100000000000000 : ℝ)*(sp1) + (1087427093/5000000000000 : ℝ)*(sp2) + (83949279/1000000000000 : ℝ)*(sp3) + (495577010991983/12500000000000 : ℝ)*(sp4) + (79292146168667/2000000000000 : ℝ)*(sp5) + (3964601943641069/100000000000000 : ℝ)*(sp6) + (471586397379667/25000000000000 : ℝ)*(sp7) + (950530883/12500000000000 : ℝ)*(sp8) + (1886353984446569/100000000000000 : ℝ)*(f.failure) + (3964623692182929/100000000000000 : ℝ)*(f.sum) + (260654618929/891250000000000000000000000 : ℝ)*base66 + (68711736784527423/44562500000000000000000000000000 : ℝ)*base67 + (227356168567472577/44562500000000000000000000000000 : ℝ)*base70 + (2558399522410077/44562500000000000000000000000000 : ℝ)*base72 + (16038318107119/3565000000000000000000000000 : ℝ)*base73 + (2239336461504722577/44562500000000000000000000000000 : ℝ)*base76 + (27123991454464923/44562500000000000000000000000000 : ℝ)*base77 + (78466232119222577/44562500000000000000000000000000 : ℝ)*base80 + (142215437708501/3565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (46603453/10000000000000000000000 : ℝ)*base89 + (46603453/10000000000000000000000 : ℝ)*base91 + (46603453/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58931/100000 : ℝ) ≤ (26262444866880968141894969120187/44562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30447173/50000000000000 : ℝ)*(lower1) + (106767129/100000000000000 : ℝ)*(upper2) + (311667/10000000000000 : ℝ)*(upper5) + (1491767332467023/50000000000000 : ℝ)*(major0) + (1491767332467023/50000000000000 : ℝ)*(major1) + (1491767332467023/50000000000000 : ℝ)*(major2) + (62761361090043/1562500000000 : ℝ)*(sp0) + (4016727964291969/100000000000000 : ℝ)*(sp1) + (1004181817793057/25000000000000 : ℝ)*(sp2) + (482673500015181/25000000000000 : ℝ)*(sp3) + (1663881293/100000000000000 : ℝ)*(sp5) + (2357001033/100000000000000 : ℝ)*(sp6) + (1049092251/100000000000000 : ℝ)*(sp7) + (251841051/10000000000000 : ℝ)*(sp12) + (965347524576487/50000000000000 : ℝ)*(f.failure) + (4016729628173261/100000000000000 : ℝ)*(f.sum) + (663620347021/111406250000000000000000000 : ℝ)*base66 + (1919143624541780771/178250000000000000000000000000000 : ℝ)*base68 + (217524288428030771/178250000000000000000000000000000 : ℝ)*base70 + (2334786231239280771/178250000000000000000000000000000 : ℝ)*base72 + (13108251336291/1782500000000000000000000000 : ℝ)*base74 + (545008675711030771/178250000000000000000000000000000 : ℝ)*base76 + (72706028530969229/178250000000000000000000000000000 : ℝ)*base77 + (138259662214280771/178250000000000000000000000000000 : ℝ)*base80 + (1278737272631/1782500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (32180781/5000000000000000000000 : ℝ)*base90 + (32180781/5000000000000000000000 : ℝ)*base92 + (32180781/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3197/4000 : ℝ) ≤ (35617726319457233766598615886739/44562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5236669/20000000000000 : ℝ)*(upper0) + (66284079/100000000000000 : ℝ)*(upper2) + (4729137/25000000000000 : ℝ)*(lower3) + (1647930825085631/50000000000000 : ℝ)*(major0) + (1647930825085631/50000000000000 : ℝ)*(major1) + (1647930825085631/50000000000000 : ℝ)*(major2) + (2378835293/100000000000000 : ℝ)*(sp0) + (80698886981/100000000000000 : ℝ)*(sp2) + (42220946331/100000000000000 : ℝ)*(sp3) + (1108067196845589/25000000000000 : ℝ)*(sp8) + (1108068430918943/25000000000000 : ℝ)*(sp9) + (554024128098599/12500000000000 : ℝ)*(sp10) + (133297801886829/6250000000000 : ℝ)*(sp11) + (2557458123/100000000000000 : ℝ)*(sp12) + (426561410227119/20000000000000 : ℝ)*(f.failure) + (1108068430918943/25000000000000 : ℝ)*(f.sum) + (4958402707339/3565000000000000000000000000 : ℝ)*base66 + (2030253055759383587/178250000000000000000000000000000 : ℝ)*base68 + (47168173937866413/178250000000000000000000000000000 : ℝ)*base69 + (659533837704883587/178250000000000000000000000000000 : ℝ)*base72 + (1860040580249/3565000000000000000000000000 : ℝ)*base74 + (927115463857133587/178250000000000000000000000000000 : ℝ)*base76 + (2182856056461383587/178250000000000000000000000000000 : ℝ)*base78 + (2147773540469633587/178250000000000000000000000000000 : ℝ)*base80 + (528564041813/111406250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (863803/2000000000000000000000 : ℝ)*base89 + (863803/2000000000000000000000 : ℝ)*base91 + (863803/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84333/100000 : ℝ) ≤ (-26142315945232604492127219/31000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22632683/25000000000000 : ℝ)*(lower1) + (112201167/50000000000000 : ℝ)*(lower2) + (188417057/100000000000000 : ℝ)*(upper5) + (333226817702009/10000000000000 : ℝ)*(major0) + (333226817702009/10000000000000 : ℝ)*(major1) + (333226817702009/10000000000000 : ℝ)*(major2) + (1272898137/6250000000000 : ℝ)*(sp0) + (95969666363/50000000000000 : ℝ)*(sp5) + (389952668329/100000000000000 : ℝ)*(sp6) + (1152127561/100000000000000 : ℝ)*(sp8) + (567032316342709/12500000000000 : ℝ)*(sp12) + (4536088109906699/100000000000000 : ℝ)*(sp13) + (4535890096571097/100000000000000 : ℝ)*(sp14) + (2156366321946159/100000000000000 : ℝ)*(sp15) + (2156366321946159/100000000000000 : ℝ)*(f.failure) + (2268140024619713/50000000000000 : ℝ)*(f.sum) + (36639952527/3875000000000000000000000 : ℝ)*base65 + (1640196000853709/1550000000000000000000000000000 : ℝ)*base67 + (823968879846291/1550000000000000000000000000000 : ℝ)*base70 + (3239339310403709/1550000000000000000000000000000 : ℝ)*base71 + (13931046909/7750000000000000000000000 : ℝ)*base73 + (4625020884646291/1550000000000000000000000000000 : ℝ)*base76 + (5809953121053709/1550000000000000000000000000000 : ℝ)*base77 + (11217362965296291/1550000000000000000000000000000 : ℝ)*base80 + (98920464479/31000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (23867717/10000000000000000000000 : ℝ)*base90 + (23867717/10000000000000000000000 : ℝ)*base92 + (23867717/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (3197/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84333/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1337_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1337_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (3197/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84333/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1337_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1337_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1337_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58931/100000 : ℝ) else (3197/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84333/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
