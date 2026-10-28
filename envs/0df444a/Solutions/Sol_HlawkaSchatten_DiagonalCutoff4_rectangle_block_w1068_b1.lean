-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:08:12.677248+00:00
-- url     : https://prove2.me/submissions/d9375073-be7e-4338-b0a4-f95fe92b75ab

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
theorem support_rectangle_w1068_s3_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2198071901/10000000000 : ℝ)*x 0 + (5437294603/10000000000 : ℝ)*x 1 + (1306149587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198071901/10000000000 : ℝ)^8261 ≤ (2668014753929/20000000000000 : ℝ)^6213 := by
    have hnat : (2198071901 : ℕ)^8261*20000000000000^6213 ≤ 2668014753929^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198071901 10000000000 2668014753929 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437294603/10000000000 : ℝ)^8261 ≤ (44479177007869/100000000000000 : ℝ)^6213 := by
    have hnat : (5437294603 : ℕ)^8261*100000000000000^6213 ≤ 44479177007869^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437294603 10000000000 44479177007869 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306149587/2500000000 : ℝ)^8261 ≤ (10545187300443/25000000000000 : ℝ)^6213 := by
    have hnat : (1306149587 : ℕ)^8261*25000000000000^6213 ≤ 10545187300443^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306149587 2500000000 10545187300443 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2198071901/10000000000 : ℝ), (5437294603/10000000000 : ℝ), (1306149587/2500000000 : ℝ)] ![(2668014753929/20000000000000 : ℝ), (44479177007869/100000000000000 : ℝ), (10545187300443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2198071901/10000000000 : ℝ)|^8261 ≤ (2668014753929/20000000000000 : ℝ)^6213
        have hw : |(-2198071901/10000000000 : ℝ)|=(2198071901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437294603/10000000000 : ℝ)|^8261 ≤ (44479177007869/100000000000000 : ℝ)^6213
        have hw : |(5437294603/10000000000 : ℝ)|=(5437294603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306149587/2500000000 : ℝ)|^8261 ≤ (10545187300443/25000000000000 : ℝ)^6213
        have hw : |(1306149587/2500000000 : ℝ)|=(1306149587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267781899/500000000 : ℝ)*x 0 + (-11534919/50000000 : ℝ)*x 1 + (5224598279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267781899/500000000 : ℝ)^8261 ≤ (43593211871081/100000000000000 : ℝ)^6213 := by
    have hnat : (267781899 : ℕ)^8261*100000000000000^6213 ≤ 43593211871081^6213*500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267781899 500000000 43593211871081 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11534919/50000000 : ℝ)^8261 ≤ (7113019827671/50000000000000 : ℝ)^6213 := by
    have hnat : (11534919 : ℕ)^8261*50000000000000^6213 ≤ 7113019827671^6213*50000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11534919 50000000 7113019827671 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224598279/10000000000 : ℝ)^8261 ≤ (42180748461073/100000000000000 : ℝ)^6213 := by
    have hnat : (5224598279 : ℕ)^8261*100000000000000^6213 ≤ 42180748461073^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224598279 10000000000 42180748461073 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267781899/500000000 : ℝ), (-11534919/50000000 : ℝ), (5224598279/10000000000 : ℝ)] ![(43593211871081/100000000000000 : ℝ), (7113019827671/50000000000000 : ℝ), (42180748461073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267781899/500000000 : ℝ)|^8261 ≤ (43593211871081/100000000000000 : ℝ)^6213
        have hw : |(267781899/500000000 : ℝ)|=(267781899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11534919/50000000 : ℝ)|^8261 ≤ (7113019827671/50000000000000 : ℝ)^6213
        have hw : |(-11534919/50000000 : ℝ)|=(11534919/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224598279/10000000000 : ℝ)|^8261 ≤ (42180748461073/100000000000000 : ℝ)^6213
        have hw : |(5224598279/10000000000 : ℝ)|=(5224598279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677818959/5000000000 : ℝ)*x 0 + (2612299057/5000000000 : ℝ)*x 1 + (-1153492049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677818959/5000000000 : ℝ)^8261 ≤ (43593211200069/100000000000000 : ℝ)^6213 := by
    have hnat : (2677818959 : ℕ)^8261*100000000000000^6213 ≤ 43593211200069^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677818959 5000000000 43593211200069 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612299057/5000000000 : ℝ)^8261 ≤ (10545186672459/25000000000000 : ℝ)^6213 := by
    have hnat : (2612299057 : ℕ)^8261*25000000000000^6213 ≤ 10545186672459^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612299057 5000000000 10545186672459 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153492049/5000000000 : ℝ)^8261 ≤ (14226042098699/100000000000000 : ℝ)^6213 := by
    have hnat : (1153492049 : ℕ)^8261*100000000000000^6213 ≤ 14226042098699^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153492049 5000000000 14226042098699 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677818959/5000000000 : ℝ), (2612299057/5000000000 : ℝ), (-1153492049/5000000000 : ℝ)] ![(43593211200069/100000000000000 : ℝ), (10545186672459/25000000000000 : ℝ), (14226042098699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677818959/5000000000 : ℝ)|^8261 ≤ (43593211200069/100000000000000 : ℝ)^6213
        have hw : |(2677818959/5000000000 : ℝ)|=(2677818959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612299057/5000000000 : ℝ)|^8261 ≤ (10545186672459/25000000000000 : ℝ)^6213
        have hw : |(2612299057/5000000000 : ℝ)|=(2612299057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1153492049/5000000000 : ℝ)|^8261 ≤ (14226042098699/100000000000000 : ℝ)^6213
        have hw : |(-1153492049/5000000000 : ℝ)|=(1153492049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186209097/5000000000 : ℝ)*x 0 + (2084467077/5000000000 : ℝ)*x 1 + (4585955621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186209097/5000000000 : ℝ)^8261 ≤ (33288350447641/100000000000000 : ℝ)^6213 := by
    have hnat : (2186209097 : ℕ)^8261*100000000000000^6213 ≤ 33288350447641^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186209097 5000000000 33288350447641 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084467077/5000000000 : ℝ)^8261 ≤ (31244483477893/100000000000000 : ℝ)^6213 := by
    have hnat : (2084467077 : ℕ)^8261*100000000000000^6213 ≤ 31244483477893^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084467077 5000000000 31244483477893 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4585955621/10000000000 : ℝ)^8261 ≤ (35467166055049/100000000000000 : ℝ)^6213 := by
    have hnat : (4585955621 : ℕ)^8261*100000000000000^6213 ≤ 35467166055049^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585955621 10000000000 35467166055049 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186209097/5000000000 : ℝ), (2084467077/5000000000 : ℝ), (4585955621/10000000000 : ℝ)] ![(33288350447641/100000000000000 : ℝ), (31244483477893/100000000000000 : ℝ), (35467166055049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186209097/5000000000 : ℝ)|^8261 ≤ (33288350447641/100000000000000 : ℝ)^6213
        have hw : |(2186209097/5000000000 : ℝ)|=(2186209097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084467077/5000000000 : ℝ)|^8261 ≤ (31244483477893/100000000000000 : ℝ)^6213
        have hw : |(2084467077/5000000000 : ℝ)|=(2084467077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4585955621/10000000000 : ℝ)|^8261 ≤ (35467166055049/100000000000000 : ℝ)^6213
        have hw : |(4585955621/10000000000 : ℝ)|=(4585955621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099047023/5000000000 : ℝ)*x 0 + (5225468061/10000000000 : ℝ)*x 1 + (5436419779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099047023/5000000000 : ℝ)^8261 ≤ (13340252469423/100000000000000 : ℝ)^6213 := by
    have hnat : (1099047023 : ℕ)^8261*100000000000000^6213 ≤ 13340252469423^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099047023 5000000000 13340252469423 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225468061/10000000000 : ℝ)^8261 ≤ (21095042812447/50000000000000 : ℝ)^6213 := by
    have hnat : (5225468061 : ℕ)^8261*50000000000000^6213 ≤ 21095042812447^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225468061 10000000000 21095042812447 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436419779/10000000000 : ℝ)^8261 ≤ (44469661886793/100000000000000 : ℝ)^6213 := by
    have hnat : (5436419779 : ℕ)^8261*100000000000000^6213 ≤ 44469661886793^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436419779 10000000000 44469661886793 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099047023/5000000000 : ℝ), (5225468061/10000000000 : ℝ), (5436419779/10000000000 : ℝ)] ![(13340252469423/100000000000000 : ℝ), (21095042812447/50000000000000 : ℝ), (44469661886793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099047023/5000000000 : ℝ)|^8261 ≤ (13340252469423/100000000000000 : ℝ)^6213
        have hw : |(-1099047023/5000000000 : ℝ)|=(1099047023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225468061/10000000000 : ℝ)|^8261 ≤ (21095042812447/50000000000000 : ℝ)^6213
        have hw : |(5225468061/10000000000 : ℝ)|=(5225468061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436419779/10000000000 : ℝ)|^8261 ≤ (44469661886793/100000000000000 : ℝ)^6213
        have hw : |(5436419779/10000000000 : ℝ)|=(5436419779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302051963/10000000000 : ℝ)*x 0 + (-2095162887/10000000000 : ℝ)*x 1 + (2718209599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302051963/10000000000 : ℝ)^8261 ≤ (43014220597537/100000000000000 : ℝ)^6213 := by
    have hnat : (5302051963 : ℕ)^8261*100000000000000^6213 ≤ 43014220597537^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302051963 10000000000 43014220597537 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095162887/10000000000 : ℝ)^8261 ≤ (12516123822483/100000000000000 : ℝ)^6213 := by
    have hnat : (2095162887 : ℕ)^8261*100000000000000^6213 ≤ 12516123822483^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095162887 10000000000 12516123822483 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718209599/5000000000 : ℝ)^8261 ≤ (44469655567649/100000000000000 : ℝ)^6213 := by
    have hnat : (2718209599 : ℕ)^8261*100000000000000^6213 ≤ 44469655567649^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718209599 5000000000 44469655567649 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302051963/10000000000 : ℝ), (-2095162887/10000000000 : ℝ), (2718209599/5000000000 : ℝ)] ![(43014220597537/100000000000000 : ℝ), (12516123822483/100000000000000 : ℝ), (44469655567649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302051963/10000000000 : ℝ)|^8261 ≤ (43014220597537/100000000000000 : ℝ)^6213
        have hw : |(5302051963/10000000000 : ℝ)|=(5302051963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095162887/10000000000 : ℝ)|^8261 ≤ (12516123822483/100000000000000 : ℝ)^6213
        have hw : |(-2095162887/10000000000 : ℝ)|=(2095162887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718209599/5000000000 : ℝ)|^8261 ≤ (44469655567649/100000000000000 : ℝ)^6213
        have hw : |(2718209599/5000000000 : ℝ)|=(2718209599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060410347/2000000000 : ℝ)*x 0 + (5436419591/10000000000 : ℝ)*x 1 + (-1047581329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060410347/2000000000 : ℝ)^8261 ≤ (43014218138109/100000000000000 : ℝ)^6213 := by
    have hnat : (1060410347 : ℕ)^8261*100000000000000^6213 ≤ 43014218138109^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060410347 2000000000 43014218138109 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436419591/10000000000 : ℝ)^8261 ≤ (11117414960511/25000000000000 : ℝ)^6213 := by
    have hnat : (5436419591 : ℕ)^8261*25000000000000^6213 ≤ 11117414960511^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436419591 10000000000 11117414960511 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047581329/5000000000 : ℝ)^8261 ≤ (6258061001771/50000000000000 : ℝ)^6213 := by
    have hnat : (1047581329 : ℕ)^8261*50000000000000^6213 ≤ 6258061001771^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047581329 5000000000 6258061001771 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060410347/2000000000 : ℝ), (5436419591/10000000000 : ℝ), (-1047581329/5000000000 : ℝ)] ![(43014218138109/100000000000000 : ℝ), (11117414960511/25000000000000 : ℝ), (6258061001771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060410347/2000000000 : ℝ)|^8261 ≤ (43014218138109/100000000000000 : ℝ)^6213
        have hw : |(1060410347/2000000000 : ℝ)|=(1060410347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436419591/10000000000 : ℝ)|^8261 ≤ (11117414960511/25000000000000 : ℝ)^6213
        have hw : |(5436419591/10000000000 : ℝ)|=(5436419591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047581329/5000000000 : ℝ)|^8261 ≤ (6258061001771/50000000000000 : ℝ)^6213
        have hw : |(-1047581329/5000000000 : ℝ)|=(1047581329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s3_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437246171/1000000000 : ℝ)*x 0 + (2292124571/5000000000 : ℝ)*x 1 + (1042662671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437246171/1000000000 : ℝ)^8261 ≤ (1664439547667/5000000000000 : ℝ)^6213 := by
    have hnat : (437246171 : ℕ)^8261*5000000000000^6213 ≤ 1664439547667^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437246171 1000000000 1664439547667 5000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292124571/5000000000 : ℝ)^8261 ≤ (8862404770397/25000000000000 : ℝ)^6213 := by
    have hnat : (2292124571 : ℕ)^8261*25000000000000^6213 ≤ 8862404770397^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292124571 5000000000 8862404770397 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042662671/2500000000 : ℝ)^8261 ≤ (31261589949803/100000000000000 : ℝ)^6213 := by
    have hnat : (1042662671 : ℕ)^8261*100000000000000^6213 ≤ 31261589949803^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042662671 2500000000 31261589949803 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437246171/1000000000 : ℝ), (2292124571/5000000000 : ℝ), (1042662671/2500000000 : ℝ)] ![(1664439547667/5000000000000 : ℝ), (8862404770397/25000000000000 : ℝ), (31261589949803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437246171/1000000000 : ℝ)|^8261 ≤ (1664439547667/5000000000000 : ℝ)^6213
        have hw : |(437246171/1000000000 : ℝ)|=(437246171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2292124571/5000000000 : ℝ)|^8261 ≤ (8862404770397/25000000000000 : ℝ)^6213
        have hw : |(2292124571/5000000000 : ℝ)|=(2292124571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042662671/2500000000 : ℝ)|^8261 ≤ (31261589949803/100000000000000 : ℝ)^6213
        have hw : |(1042662671/2500000000 : ℝ)|=(1042662671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14903/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4361/50000 : ℝ) ^ (2065/512 : ℝ) ≤ (1334226251626431/25000000000000000000 : ℝ) := by
    have hpowers : (4361/50000 : ℝ)^2065 ≤ (1334226251626431/25000000000000000000 : ℝ)^512 := by
      have hnat : (4361 : ℕ)^2065*25000000000000000000^512 ≤ 1334226251626431^512*50000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4361 50000 1334226251626431 25000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4361/50000 : ℝ)) (X := (1334226251626431/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8367/50000 : ℝ) ^ (2065/512 : ℝ) ≤ (36947933123552361/50000000000000000000 : ℝ) := by
    have hpowers : (8367/50000 : ℝ)^2065 ≤ (36947933123552361/50000000000000000000 : ℝ)^512 := by
      have hnat : (8367 : ℕ)^2065*50000000000000000000^512 ≤ 36947933123552361^512*50000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8367 50000 36947933123552361 50000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8367/50000 : ℝ)) (X := (36947933123552361/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501334226251626431/12500000000000000000 : ℝ) ≤ (5000132318919953/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (12501334226251626431/12500000000000000000 : ℝ)^512 ≤ (5000132318919953/5000000000000000 : ℝ)^2065 := by
      have hnat : (12501334226251626431 : ℕ)^512*5000000000000000^2065 ≤ 5000132318919953^2065*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501334226251626431 12500000000000000000 5000132318919953 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132318919953/5000000000000000 : ℝ)) (X := (12501334226251626431/12500000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50039616385626805223/50000000000000000000 : ℝ) ≤ (16003142283619/16000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50039616385626805223/50000000000000000000 : ℝ)^512 ≤ (16003142283619/16000000000000 : ℝ)^2065 := by
      have hnat : (50039616385626805223 : ℕ)^512*16000000000000^2065 ≤ 16003142283619^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039616385626805223 50000000000000000000 16003142283619 16000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16003142283619/16000000000000 : ℝ)) (X := (50039616385626805223/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25036947933123552361/25000000000000000000 : ℝ) ≤ (2500915804170961/2500000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (25036947933123552361/25000000000000000000 : ℝ)^512 ≤ (2500915804170961/2500000000000000 : ℝ)^2065 := by
      have hnat : (25036947933123552361 : ℕ)^512*2500000000000000^2065 ≤ 2500915804170961^2065*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036947933123552361 25000000000000000000 2500915804170961 2500000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500915804170961/2500000000000000 : ℝ)) (X := (25036947933123552361/25000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1334226251626431/25000000000000000000 : ℝ) ≤ ((20023119468424124909/20030000000000000000 : ℝ)+2*(1699289421969/801200000000000 : ℝ)*(4361/50000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (20023119468424124909/20030000000000000000 : ℝ)+2*(1699289421969/801200000000000 : ℝ)*(4361/50000 : ℝ)=(5000132318919953/5000000000000000 : ℝ) by norm_num, show 1+2*(1334226251626431/25000000000000000000 : ℝ)=(12501334226251626431/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36947933123552361/50000000000000000000 : ℝ)+(1334226251626431/25000000000000000000 : ℝ) ≤ ((20023119468424124909/20030000000000000000 : ℝ)+(1699289421969/801200000000000 : ℝ)*((8367/50000 : ℝ)+(4361/50000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (20023119468424124909/20030000000000000000 : ℝ)+(1699289421969/801200000000000 : ℝ)*((8367/50000 : ℝ)+(4361/50000 : ℝ))=(16003142283619/16000000000000 : ℝ) by norm_num, show 1+(36947933123552361/50000000000000000000 : ℝ)+(1334226251626431/25000000000000000000 : ℝ)=(50039616385626805223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36947933123552361/50000000000000000000 : ℝ) ≤ ((20023119468424124909/20030000000000000000 : ℝ)+2*(1699289421969/801200000000000 : ℝ)*(8367/50000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (20023119468424124909/20030000000000000000 : ℝ)+2*(1699289421969/801200000000000 : ℝ)*(8367/50000 : ℝ)=(2500915804170961/2500000000000000 : ℝ) by norm_num, show 1+2*(36947933123552361/50000000000000000000 : ℝ)=(25036947933123552361/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20023119468424124909/20030000000000000000 : ℝ)*(X 1 0+X 2 0)+(1699289421969/801200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (4361/50000 : ℝ)) (hi := (8367/50000 : ℝ)) (c := (20023119468424124909/20030000000000000000 : ℝ)) (alpha := (1699289421969/801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20023119468424124909/20030000000000000000 : ℝ)*(X 0 1+X 2 1)+(1699289421969/801200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (4361/50000 : ℝ)) (hi := (8367/50000 : ℝ)) (c := (20023119468424124909/20030000000000000000 : ℝ)) (alpha := (1699289421969/801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20023119468424124909/20030000000000000000 : ℝ)*(X 0 2+X 1 2)+(1699289421969/801200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (4361/50000 : ℝ)) (hi := (8367/50000 : ℝ)) (c := (20023119468424124909/20030000000000000000 : ℝ)) (alpha := (1699289421969/801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2198071901/10000000000 : ℝ)*X 0 0+(5437294603/10000000000 : ℝ)*X 0 1+(1306149587/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267781899/500000000 : ℝ)*X 1 0+(-11534919/50000000 : ℝ)*X 1 1+(5224598279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677818959/5000000000 : ℝ)*X 2 0+(2612299057/5000000000 : ℝ)*X 2 1+(-1153492049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186209097/5000000000 : ℝ)*X 0 0+(2084467077/5000000000 : ℝ)*X 0 1+(4585955621/10000000000 : ℝ)*X 0 2+(2186209097/5000000000 : ℝ)*X 1 0+(2084467077/5000000000 : ℝ)*X 1 1+(4585955621/10000000000 : ℝ)*X 1 2+(2186209097/5000000000 : ℝ)*X 2 0+(2084467077/5000000000 : ℝ)*X 2 1+(4585955621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1099047023/5000000000 : ℝ)*X 0 0+(5225468061/10000000000 : ℝ)*X 0 1+(5436419779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302051963/10000000000 : ℝ)*X 1 0+(-2095162887/10000000000 : ℝ)*X 1 1+(2718209599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060410347/2000000000 : ℝ)*X 2 0+(5436419591/10000000000 : ℝ)*X 2 1+(-1047581329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437246171/1000000000 : ℝ)*X 0 0+(2292124571/5000000000 : ℝ)*X 0 1+(1042662671/2500000000 : ℝ)*X 0 2+(437246171/1000000000 : ℝ)*X 1 0+(2292124571/5000000000 : ℝ)*X 1 1+(1042662671/2500000000 : ℝ)*X 1 2+(437246171/1000000000 : ℝ)*X 2 0+(2292124571/5000000000 : ℝ)*X 2 1+(1042662671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38180700165306665339943/10015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (725675343/100000000000000 : ℝ)*(base19) + (719742749/100000000000000 : ℝ)*(base23) + (6820437/20000000000000 : ℝ)*(upper2) + (196139617/100000000000000 : ℝ)*(upper3) + (887441371889307/25000000000000 : ℝ)*(major0) + (887441371889307/25000000000000 : ℝ)*(major1) + (887441371889307/25000000000000 : ℝ)*(major2) + (940310541356073/20000000000000 : ℝ)*(sp0) + (2350778774944043/50000000000000 : ℝ)*(sp1) + (940311207734759/20000000000000 : ℝ)*(sp2) + (299745531972869/12500000000000 : ℝ)*(sp3) + (1113756613/20000000000000 : ℝ)*(sp4) + (379286721/25000000000000 : ℝ)*(sp6) + (8316689683/100000000000000 : ℝ)*(sp7) + (599493143118159/25000000000000 : ℝ)*(f.failure) + (4701558275563429/100000000000000 : ℝ)*(f.sum) + (3661815589519/5007500000000000000000000000 : ℝ)*base65 + (930959215113976937/500750000000000000000000000000000 : ℝ)*base68 + (1320615005887726937/500750000000000000000000000000000 : ℝ)*base70 + (2140005690546976937/500750000000000000000000000000000 : ℝ)*base72 + (35570677978573/10015000000000000000000000000 : ℝ)*base73 + (4761432231358023063/500750000000000000000000000000000 : ℝ)*base75 + (2183521752250523063/500750000000000000000000000000000 : ℝ)*base77 + (5025777500375523063/500750000000000000000000000000000 : ℝ)*base79 + (21487995713753/10015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (27825573/2500000000000000000000 : ℝ)*base89 + (27825573/2500000000000000000000 : ℝ)*base91 + (27825573/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518337052235754424289906691/62593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1624910587/100000000000000 : ℝ)*(base19) + (1432236487/100000000000000 : ℝ)*(base23) + (5387613/50000000000000 : ℝ)*(upper3) + (108563/500000000000 : ℝ)*(lower4) + (44803851/12500000000000 : ℝ)*(upper5) + (447389318122117/12500000000000 : ℝ)*(major0) + (447389318122117/12500000000000 : ℝ)*(major1) + (447389318122117/12500000000000 : ℝ)*(major2) + (21496784407/100000000000000 : ℝ)*(sp1) + (9275251971/50000000000000 : ℝ)*(sp2) + (1185107519221179/25000000000000 : ℝ)*(sp4) + (2370203477594861/50000000000000 : ℝ)*(sp5) + (2370205047072143/50000000000000 : ℝ)*(sp6) + (1208899368518383/50000000000000 : ℝ)*(sp7) + (1208899368518383/50000000000000 : ℝ)*(f.failure) + (1185107519221179/25000000000000 : ℝ)*(f.sum) + (23594370751443/5007500000000000000000000000 : ℝ)*base65 + (1105291894714837353/250375000000000000000000000000000 : ℝ)*base67 + (853250333507662647/250375000000000000000000000000000 : ℝ)*base70 + (614776834630587353/250375000000000000000000000000000 : ℝ)*base71 + (47952041099/9780273437500000000000000 : ℝ)*base73 + (24534184962962353/250375000000000000000000000000000 : ℝ)*base75 + (1080021952073087353/250375000000000000000000000000000 : ℝ)*base77 + (3089058903938087353/250375000000000000000000000000000 : ℝ)*base79 + (6201418572427/5007500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (59218299/5000000000000000000000 : ℝ)*base90 + (59218299/5000000000000000000000 : ℝ)*base92 + (59218299/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14903/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s4_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201728723/10000000000 : ℝ)*x 0 + (5405701619/10000000000 : ℝ)*x 1 + (5253802417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201728723/10000000000 : ℝ)^8261 ≤ (3342397662373/25000000000000 : ℝ)^6213 := by
    have hnat : (2201728723 : ℕ)^8261*25000000000000^6213 ≤ 3342397662373^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201728723 10000000000 3342397662373 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405701619/10000000000 : ℝ)^8261 ≤ (44135872780151/100000000000000 : ℝ)^6213 := by
    have hnat : (5405701619 : ℕ)^8261*100000000000000^6213 ≤ 44135872780151^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405701619 10000000000 44135872780151 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253802417/10000000000 : ℝ)^8261 ≤ (21247268277897/50000000000000 : ℝ)^6213 := by
    have hnat : (5253802417 : ℕ)^8261*50000000000000^6213 ≤ 21247268277897^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253802417 10000000000 21247268277897 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201728723/10000000000 : ℝ), (5405701619/10000000000 : ℝ), (5253802417/10000000000 : ℝ)] ![(3342397662373/25000000000000 : ℝ), (44135872780151/100000000000000 : ℝ), (21247268277897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201728723/10000000000 : ℝ)|^8261 ≤ (3342397662373/25000000000000 : ℝ)^6213
        have hw : |(-2201728723/10000000000 : ℝ)|=(2201728723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405701619/10000000000 : ℝ)|^8261 ≤ (44135872780151/100000000000000 : ℝ)^6213
        have hw : |(5405701619/10000000000 : ℝ)|=(5405701619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253802417/10000000000 : ℝ)|^8261 ≤ (21247268277897/50000000000000 : ℝ)^6213
        have hw : |(5253802417/10000000000 : ℝ)|=(5253802417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673905147/5000000000 : ℝ)*x 0 + (-2278986979/10000000000 : ℝ)*x 1 + (2626901189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673905147/5000000000 : ℝ)^8261 ≤ (10877128735913/25000000000000 : ℝ)^6213 := by
    have hnat : (2673905147 : ℕ)^8261*25000000000000^6213 ≤ 10877128735913^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673905147 5000000000 10877128735913 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278986979/10000000000 : ℝ)^8261 ≤ (13996948900881/100000000000000 : ℝ)^6213 := by
    have hnat : (2278986979 : ℕ)^8261*100000000000000^6213 ≤ 13996948900881^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278986979 10000000000 13996948900881 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626901189/5000000000 : ℝ)^8261 ≤ (2655908508523/6250000000000 : ℝ)^6213 := by
    have hnat : (2626901189 : ℕ)^8261*6250000000000^6213 ≤ 2655908508523^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626901189 5000000000 2655908508523 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673905147/5000000000 : ℝ), (-2278986979/10000000000 : ℝ), (2626901189/5000000000 : ℝ)] ![(10877128735913/25000000000000 : ℝ), (13996948900881/100000000000000 : ℝ), (2655908508523/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673905147/5000000000 : ℝ)|^8261 ≤ (10877128735913/25000000000000 : ℝ)^6213
        have hw : |(2673905147/5000000000 : ℝ)|=(2673905147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2278986979/10000000000 : ℝ)|^8261 ≤ (13996948900881/100000000000000 : ℝ)^6213
        have hw : |(-2278986979/10000000000 : ℝ)|=(2278986979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626901189/5000000000 : ℝ)|^8261 ≤ (2655908508523/6250000000000 : ℝ)^6213
        have hw : |(2626901189/5000000000 : ℝ)|=(2626901189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668476299/1250000000 : ℝ)*x 0 + (2626901167/5000000000 : ℝ)*x 1 + (-2278986907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668476299/1250000000 : ℝ)^8261 ≤ (43508516003773/100000000000000 : ℝ)^6213 := by
    have hnat : (668476299 : ℕ)^8261*100000000000000^6213 ≤ 43508516003773^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668476299 1250000000 43508516003773 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626901167/5000000000 : ℝ)^8261 ≤ (4249453566317/10000000000000 : ℝ)^6213 := by
    have hnat : (2626901167 : ℕ)^8261*10000000000000^6213 ≤ 4249453566317^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626901167 5000000000 4249453566317 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278986907/10000000000 : ℝ)^8261 ≤ (13996948312911/100000000000000 : ℝ)^6213 := by
    have hnat : (2278986907 : ℕ)^8261*100000000000000^6213 ≤ 13996948312911^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278986907 10000000000 13996948312911 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668476299/1250000000 : ℝ), (2626901167/5000000000 : ℝ), (-2278986907/10000000000 : ℝ)] ![(43508516003773/100000000000000 : ℝ), (4249453566317/10000000000000 : ℝ), (13996948312911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668476299/1250000000 : ℝ)|^8261 ≤ (43508516003773/100000000000000 : ℝ)^6213
        have hw : |(668476299/1250000000 : ℝ)|=(668476299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626901167/5000000000 : ℝ)|^8261 ≤ (4249453566317/10000000000000 : ℝ)^6213
        have hw : |(2626901167/5000000000 : ℝ)|=(2626901167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278986907/10000000000 : ℝ)|^8261 ≤ (13996948312911/100000000000000 : ℝ)^6213
        have hw : |(-2278986907/10000000000 : ℝ)|=(2278986907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093648563/2500000000 : ℝ)*x 0 + (4228249687/10000000000 : ℝ)*x 1 + (1131517311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093648563/2500000000 : ℝ)^8261 ≤ (33310380114777/100000000000000 : ℝ)^6213 := by
    have hnat : (1093648563 : ℕ)^8261*100000000000000^6213 ≤ 33310380114777^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093648563 2500000000 33310380114777 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228249687/10000000000 : ℝ)^8261 ≤ (3183694757099/10000000000000 : ℝ)^6213 := by
    have hnat : (4228249687 : ℕ)^8261*10000000000000^6213 ≤ 3183694757099^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228249687 10000000000 3183694757099 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131517311/2500000000 : ℝ)^8261 ≤ (544573004673/1562500000000 : ℝ)^6213 := by
    have hnat : (1131517311 : ℕ)^8261*1562500000000^6213 ≤ 544573004673^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131517311 2500000000 544573004673 1562500000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093648563/2500000000 : ℝ), (4228249687/10000000000 : ℝ), (1131517311/2500000000 : ℝ)] ![(33310380114777/100000000000000 : ℝ), (3183694757099/10000000000000 : ℝ), (544573004673/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093648563/2500000000 : ℝ)|^8261 ≤ (33310380114777/100000000000000 : ℝ)^6213
        have hw : |(1093648563/2500000000 : ℝ)|=(1093648563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228249687/10000000000 : ℝ)|^8261 ≤ (3183694757099/10000000000000 : ℝ)^6213
        have hw : |(4228249687/10000000000 : ℝ)|=(4228249687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131517311/2500000000 : ℝ)|^8261 ≤ (544573004673/1562500000000 : ℝ)^6213
        have hw : |(1131517311/2500000000 : ℝ)|=(1131517311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-275217109/1250000000 : ℝ)*x 0 + (1313561809/2500000000 : ℝ)*x 1 + (2702627443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275217109/1250000000 : ℝ)^8261 ≤ (13369656444077/100000000000000 : ℝ)^6213 := by
    have hnat : (275217109 : ℕ)^8261*100000000000000^6213 ≤ 13369656444077^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275217109 1250000000 13369656444077 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313561809/2500000000 : ℝ)^8261 ≤ (21249660216477/50000000000000 : ℝ)^6213 := by
    have hnat : (1313561809 : ℕ)^8261*50000000000000^6213 ≤ 21249660216477^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313561809 2500000000 21249660216477 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702627443/5000000000 : ℝ)^8261 ≤ (44131023100667/100000000000000 : ℝ)^6213 := by
    have hnat : (2702627443 : ℕ)^8261*100000000000000^6213 ≤ 44131023100667^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702627443 5000000000 44131023100667 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275217109/1250000000 : ℝ), (1313561809/2500000000 : ℝ), (2702627443/5000000000 : ℝ)] ![(13369656444077/100000000000000 : ℝ), (21249660216477/50000000000000 : ℝ), (44131023100667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275217109/1250000000 : ℝ)|^8261 ≤ (13369656444077/100000000000000 : ℝ)^6213
        have hw : |(-275217109/1250000000 : ℝ)|=(275217109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313561809/2500000000 : ℝ)|^8261 ≤ (21249660216477/50000000000000 : ℝ)^6213
        have hw : |(1313561809/2500000000 : ℝ)|=(1313561809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702627443/5000000000 : ℝ)|^8261 ≤ (44131023100667/100000000000000 : ℝ)^6213
        have hw : |(2702627443/5000000000 : ℝ)|=(2702627443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654773143/5000000000 : ℝ)*x 0 + (-106376691/500000000 : ℝ)*x 1 + (5405254751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654773143/5000000000 : ℝ)^8261 ≤ (43095080438841/100000000000000 : ℝ)^6213 := by
    have hnat : (2654773143 : ℕ)^8261*100000000000000^6213 ≤ 43095080438841^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654773143 5000000000 43095080438841 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106376691/500000000 : ℝ)^8261 ≤ (6386948957177/50000000000000 : ℝ)^6213 := by
    have hnat : (106376691 : ℕ)^8261*50000000000000^6213 ≤ 6386948957177^6213*500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106376691 500000000 6386948957177 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405254751/10000000000 : ℝ)^8261 ≤ (44131021635143/100000000000000 : ℝ)^6213 := by
    have hnat : (5405254751 : ℕ)^8261*100000000000000^6213 ≤ 44131021635143^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405254751 10000000000 44131021635143 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654773143/5000000000 : ℝ), (-106376691/500000000 : ℝ), (5405254751/10000000000 : ℝ)] ![(43095080438841/100000000000000 : ℝ), (6386948957177/50000000000000 : ℝ), (44131021635143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654773143/5000000000 : ℝ)|^8261 ≤ (43095080438841/100000000000000 : ℝ)^6213
        have hw : |(2654773143/5000000000 : ℝ)|=(2654773143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106376691/500000000 : ℝ)|^8261 ≤ (6386948957177/50000000000000 : ℝ)^6213
        have hw : |(-106376691/500000000 : ℝ)|=(106376691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405254751/10000000000 : ℝ)|^8261 ≤ (44131021635143/100000000000000 : ℝ)^6213
        have hw : |(5405254751/10000000000 : ℝ)|=(5405254751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530954577/1000000000 : ℝ)*x 0 + (2702627483/5000000000 : ℝ)*x 1 + (-85101369/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530954577/1000000000 : ℝ)^8261 ≤ (21547537435087/50000000000000 : ℝ)^6213 := by
    have hnat : (530954577 : ℕ)^8261*50000000000000^6213 ≤ 21547537435087^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530954577 1000000000 21547537435087 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702627483/5000000000 : ℝ)^8261 ≤ (22065511984563/50000000000000 : ℝ)^6213 := by
    have hnat : (2702627483 : ℕ)^8261*50000000000000^6213 ≤ 22065511984563^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702627483 5000000000 22065511984563 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85101369/400000000 : ℝ)^8261 ≤ (12773901147559/100000000000000 : ℝ)^6213 := by
    have hnat : (85101369 : ℕ)^8261*100000000000000^6213 ≤ 12773901147559^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85101369 400000000 12773901147559 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530954577/1000000000 : ℝ), (2702627483/5000000000 : ℝ), (-85101369/400000000 : ℝ)] ![(21547537435087/50000000000000 : ℝ), (22065511984563/50000000000000 : ℝ), (12773901147559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530954577/1000000000 : ℝ)|^8261 ≤ (21547537435087/50000000000000 : ℝ)^6213
        have hw : |(530954577/1000000000 : ℝ)|=(530954577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702627483/5000000000 : ℝ)|^8261 ≤ (22065511984563/50000000000000 : ℝ)^6213
        have hw : |(2702627483/5000000000 : ℝ)|=(2702627483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85101369/400000000 : ℝ)|^8261 ≤ (12773901147559/100000000000000 : ℝ)^6213
        have hw : |(-85101369/400000000 : ℝ)|=(85101369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s4_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187304879/5000000000 : ℝ)*x 0 + (14141241/31250000 : ℝ)*x 1 + (4229125861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187304879/5000000000 : ℝ)^8261 ≤ (33310537105183/100000000000000 : ℝ)^6213 := by
    have hnat : (2187304879 : ℕ)^8261*100000000000000^6213 ≤ 33310537105183^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187304879 5000000000 33310537105183 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14141241/31250000 : ℝ)^8261 ≤ (34843743139129/100000000000000 : ℝ)^6213 := by
    have hnat : (14141241 : ℕ)^8261*100000000000000^6213 ≤ 34843743139129^6213*31250000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14141241 31250000 34843743139129 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229125861/10000000000 : ℝ)^8261 ≤ (31845719745413/100000000000000 : ℝ)^6213 := by
    have hnat : (4229125861 : ℕ)^8261*100000000000000^6213 ≤ 31845719745413^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229125861 10000000000 31845719745413 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187304879/5000000000 : ℝ), (14141241/31250000 : ℝ), (4229125861/10000000000 : ℝ)] ![(33310537105183/100000000000000 : ℝ), (34843743139129/100000000000000 : ℝ), (31845719745413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187304879/5000000000 : ℝ)|^8261 ≤ (33310537105183/100000000000000 : ℝ)^6213
        have hw : |(2187304879/5000000000 : ℝ)|=(2187304879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14141241/31250000 : ℝ)|^8261 ≤ (34843743139129/100000000000000 : ℝ)^6213
        have hw : |(14141241/31250000 : ℝ)|=(14141241/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229125861/10000000000 : ℝ)|^8261 ≤ (31845719745413/100000000000000 : ℝ)^6213
        have hw : |(4229125861/10000000000 : ℝ)|=(4229125861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14243/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14903/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14903/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14903/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14903/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14903/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14903/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10403/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (5432140476462633/50000000000000000000 : ℝ) := by
    have hpowers : (10403/100000 : ℝ)^2065 ≤ (5432140476462633/50000000000000000000 : ℝ)^512 := by
      have hnat : (10403 : ℕ)^2065*50000000000000000000^512 ≤ 5432140476462633^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10403 100000 5432140476462633 50000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10403/100000 : ℝ)) (X := (5432140476462633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14903/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (46306814796785643/100000000000000000000 : ℝ) := by
    have hpowers : (14903/100000 : ℝ)^2065 ≤ (46306814796785643/100000000000000000000 : ℝ)^512 := by
      have hnat : (14903 : ℕ)^2065*100000000000000000000^512 ≤ 46306814796785643^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14903 100000 46306814796785643 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14903/100000 : ℝ)) (X := (46306814796785643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005432140476462633/25000000000000000000 : ℝ) ≤ (10000538698054877/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (25005432140476462633/25000000000000000000 : ℝ)^512 ≤ (10000538698054877/10000000000000000 : ℝ)^2065 := by
      have hnat : (25005432140476462633 : ℕ)^512*10000000000000000^2065 ≤ 10000538698054877^2065*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005432140476462633 25000000000000000000 10000538698054877 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538698054877/10000000000000000 : ℝ)) (X := (25005432140476462633/25000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057171095749710909/100000000000000000000 : ℝ) ≤ (625088575394423/625000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (100057171095749710909/100000000000000000000 : ℝ)^512 ≤ (625088575394423/625000000000000 : ℝ)^2065 := by
      have hnat : (100057171095749710909 : ℕ)^512*625000000000000^2065 ≤ 625088575394423^2065*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057171095749710909 100000000000000000000 625088575394423 625000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625088575394423/625000000000000 : ℝ)) (X := (100057171095749710909/100000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046306814796785643/50000000000000000000 : ℝ) ≤ (10002295714566659/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50046306814796785643/50000000000000000000 : ℝ)^512 ≤ (10002295714566659/10000000000000000 : ℝ)^2065 := by
      have hnat : (50046306814796785643 : ℕ)^512*10000000000000000^2065 ≤ 10002295714566659^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046306814796785643 50000000000000000000 10002295714566659 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002295714566659/10000000000000000 : ℝ)) (X := (50046306814796785643/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5432140476462633/50000000000000000000 : ℝ) ≤ ((7497357649745813059/7500000000000000000 : ℝ)+2*(292836085297/150000000000000 : ℝ)*(10403/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (7497357649745813059/7500000000000000000 : ℝ)+2*(292836085297/150000000000000 : ℝ)*(10403/100000 : ℝ)=(10000538698054877/10000000000000000 : ℝ) by norm_num, show 1+2*(5432140476462633/50000000000000000000 : ℝ)=(25005432140476462633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46306814796785643/100000000000000000000 : ℝ)+(5432140476462633/50000000000000000000 : ℝ) ≤ ((7497357649745813059/7500000000000000000 : ℝ)+(292836085297/150000000000000 : ℝ)*((14903/100000 : ℝ)+(10403/100000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (7497357649745813059/7500000000000000000 : ℝ)+(292836085297/150000000000000 : ℝ)*((14903/100000 : ℝ)+(10403/100000 : ℝ))=(625088575394423/625000000000000 : ℝ) by norm_num, show 1+(46306814796785643/100000000000000000000 : ℝ)+(5432140476462633/50000000000000000000 : ℝ)=(100057171095749710909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46306814796785643/100000000000000000000 : ℝ) ≤ ((7497357649745813059/7500000000000000000 : ℝ)+2*(292836085297/150000000000000 : ℝ)*(14903/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (7497357649745813059/7500000000000000000 : ℝ)+2*(292836085297/150000000000000 : ℝ)*(14903/100000 : ℝ)=(10002295714566659/10000000000000000 : ℝ) by norm_num, show 1+2*(46306814796785643/100000000000000000000 : ℝ)=(50046306814796785643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7497357649745813059/7500000000000000000 : ℝ)*(X 1 0+X 2 0)+(292836085297/150000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (14903/100000 : ℝ)) (c := (7497357649745813059/7500000000000000000 : ℝ)) (alpha := (292836085297/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7497357649745813059/7500000000000000000 : ℝ)*(X 0 1+X 2 1)+(292836085297/150000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (14903/100000 : ℝ)) (c := (7497357649745813059/7500000000000000000 : ℝ)) (alpha := (292836085297/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7497357649745813059/7500000000000000000 : ℝ)*(X 0 2+X 1 2)+(292836085297/150000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (14903/100000 : ℝ)) (c := (7497357649745813059/7500000000000000000 : ℝ)) (alpha := (292836085297/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201728723/10000000000 : ℝ)*X 0 0+(5405701619/10000000000 : ℝ)*X 0 1+(5253802417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673905147/5000000000 : ℝ)*X 1 0+(-2278986979/10000000000 : ℝ)*X 1 1+(2626901189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668476299/1250000000 : ℝ)*X 2 0+(2626901167/5000000000 : ℝ)*X 2 1+(-2278986907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093648563/2500000000 : ℝ)*X 0 0+(4228249687/10000000000 : ℝ)*X 0 1+(1131517311/2500000000 : ℝ)*X 0 2+(1093648563/2500000000 : ℝ)*X 1 0+(4228249687/10000000000 : ℝ)*X 1 1+(1131517311/2500000000 : ℝ)*X 1 2+(1093648563/2500000000 : ℝ)*X 2 0+(4228249687/10000000000 : ℝ)*X 2 1+(1131517311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-275217109/1250000000 : ℝ)*X 0 0+(1313561809/2500000000 : ℝ)*X 0 1+(2702627443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654773143/5000000000 : ℝ)*X 1 0+(-106376691/500000000 : ℝ)*X 1 1+(5405254751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530954577/1000000000 : ℝ)*X 2 0+(2702627483/5000000000 : ℝ)*X 2 1+(-85101369/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187304879/5000000000 : ℝ)*X 0 0+(14141241/31250000 : ℝ)*X 0 1+(4229125861/10000000000 : ℝ)*X 0 2+(2187304879/5000000000 : ℝ)*X 1 0+(14141241/31250000 : ℝ)*X 1 1+(4229125861/10000000000 : ℝ)*X 1 2+(2187304879/5000000000 : ℝ)*X 2 0+(14141241/31250000 : ℝ)*X 2 1+(4229125861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12855401058494853745899/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362730457/20000000000000 : ℝ)*(base19) + (1549599759/100000000000000 : ℝ)*(base23) + (205727491/100000000000000 : ℝ)*(lower2) + (128339817/50000000000000 : ℝ)*(upper3) + (85502677/100000000000000 : ℝ)*(upper5) + (2485292216290683/50000000000000 : ℝ)*(major0) + (2485292216290683/50000000000000 : ℝ)*(major1) + (2485292216290683/50000000000000 : ℝ)*(major2) + (6583352138148103/100000000000000 : ℝ)*(sp0) + (41146178233501/625000000000 : ℝ)*(sp1) + (6583388781412687/100000000000000 : ℝ)*(sp2) + (419719411975079/12500000000000 : ℝ)*(sp3) + (19096432171/50000000000000 : ℝ)*(sp4) + (22895538949/100000000000000 : ℝ)*(sp7) + (167888909566979/5000000000000 : ℝ)*(f.failure) + (3291695165506223/50000000000000 : ℝ)*(f.sum) + (7090627178633/1250000000000000000000000000 : ℝ)*base66 + (1242773187006901/125000000000000000000000000000000 : ℝ)*base68 + (1667620260937993099/125000000000000000000000000000000 : ℝ)*base69 + (377449287312006901/125000000000000000000000000000000 : ℝ)*base72 + (1076220932617/1250000000000000000000000000 : ℝ)*base73 + (2103317696312993099/125000000000000000000000000000000 : ℝ)*base75 + (1955668820312006901/125000000000000000000000000000000 : ℝ)*base78 + (642197978187993099/125000000000000000000000000000000 : ℝ)*base79 + (4169644977617/1250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1721887/500000000000000000000 : ℝ)*base90 + (1721887/500000000000000000000 : ℝ)*base92 + (1721887/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19972963674532962867631/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1266069757/50000000000000 : ℝ)*(base19) + (1782464173/100000000000000 : ℝ)*(base23) + (1068971/2500000000000 : ℝ)*(upper3) + (1524001/5000000000000 : ℝ)*(lower4) + (26659181/25000000000000 : ℝ)*(upper5) + (4999868225451077/100000000000000 : ℝ)*(major0) + (4999868225451077/100000000000000 : ℝ)*(major1) + (4999868225451077/100000000000000 : ℝ)*(major2) + (68093709211/100000000000000 : ℝ)*(sp1) + (22701700243/50000000000000 : ℝ)*(sp2) + (1655543979211097/25000000000000 : ℝ)*(sp4) + (6622105290995663/100000000000000 : ℝ)*(sp5) + (6622128730979729/100000000000000 : ℝ)*(sp6) + (168878013387579/5000000000000 : ℝ)*(sp7) + (168878013387579/5000000000000 : ℝ)*(f.failure) + (1655543979211097/25000000000000 : ℝ)*(f.sum) + (4295347734869/7500000000000000000000000000 : ℝ)*base65 + (1660109569288111819/250000000000000000000000000000000 : ℝ)*base68 + (5258185711888181/250000000000000000000000000000000 : ℝ)*base69 + (687507399711888181/250000000000000000000000000000000 : ℝ)*base71 + (2171302767631/7500000000000000000000000000 : ℝ)*base74 + (1645934040038111819/250000000000000000000000000000000 : ℝ)*base76 + (2616464602211888181/250000000000000000000000000000000 : ℝ)*base77 + (2063861311788111819/250000000000000000000000000000000 : ℝ)*base80 + (7599808367369/7500000000000000000000000000 : ℝ)*base81 + (13687/500000000000000000000 : ℝ)*base90 + (13687/500000000000000000000 : ℝ)*base92 + (13687/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s5_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-440510747/2000000000 : ℝ)*x 0 + (1349235849/2500000000 : ℝ)*x 1 + (2631009709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440510747/2000000000 : ℝ)^8261 ≤ (2675250431807/20000000000000 : ℝ)^6213 := by
    have hnat : (440510747 : ℕ)^8261*20000000000000^6213 ≤ 2675250431807^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440510747 2000000000 2675250431807 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349235849/2500000000 : ℝ)^8261 ≤ (220204093363/500000000000 : ℝ)^6213 := by
    have hnat : (1349235849 : ℕ)^8261*500000000000^6213 ≤ 220204093363^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349235849 2500000000 220204093363 500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631009709/5000000000 : ℝ)^8261 ≤ (42582929147073/100000000000000 : ℝ)^6213 := by
    have hnat : (2631009709 : ℕ)^8261*100000000000000^6213 ≤ 42582929147073^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631009709 5000000000 42582929147073 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440510747/2000000000 : ℝ), (1349235849/2500000000 : ℝ), (2631009709/5000000000 : ℝ)] ![(2675250431807/20000000000000 : ℝ), (220204093363/500000000000 : ℝ), (42582929147073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440510747/2000000000 : ℝ)|^8261 ≤ (2675250431807/20000000000000 : ℝ)^6213
        have hw : |(-440510747/2000000000 : ℝ)|=(440510747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349235849/2500000000 : ℝ)|^8261 ≤ (220204093363/500000000000 : ℝ)^6213
        have hw : |(1349235849/2500000000 : ℝ)|=(1349235849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631009709/5000000000 : ℝ)|^8261 ≤ (42582929147073/100000000000000 : ℝ)^6213
        have hw : |(2631009709/5000000000 : ℝ)|=(2631009709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668203557/1250000000 : ℝ)*x 0 + (-283881033/1250000000 : ℝ)*x 1 + (5262019407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668203557/1250000000 : ℝ)^8261 ≤ (543561429441/1250000000000 : ℝ)^6213 := by
    have hnat : (668203557 : ℕ)^8261*1250000000000^6213 ≤ 543561429441^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668203557 1250000000 543561429441 1250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283881033/1250000000 : ℝ)^8261 ≤ (13932156599339/100000000000000 : ℝ)^6213 := by
    have hnat : (283881033 : ℕ)^8261*100000000000000^6213 ≤ 13932156599339^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283881033 1250000000 13932156599339 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262019407/10000000000 : ℝ)^8261 ≤ (42582929028713/100000000000000 : ℝ)^6213 := by
    have hnat : (5262019407 : ℕ)^8261*100000000000000^6213 ≤ 42582929028713^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262019407 10000000000 42582929028713 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668203557/1250000000 : ℝ), (-283881033/1250000000 : ℝ), (5262019407/10000000000 : ℝ)] ![(543561429441/1250000000000 : ℝ), (13932156599339/100000000000000 : ℝ), (42582929028713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668203557/1250000000 : ℝ)|^8261 ≤ (543561429441/1250000000000 : ℝ)^6213
        have hw : |(668203557/1250000000 : ℝ)|=(668203557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283881033/1250000000 : ℝ)|^8261 ≤ (13932156599339/100000000000000 : ℝ)^6213
        have hw : |(-283881033/1250000000 : ℝ)|=(283881033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262019407/10000000000 : ℝ)|^8261 ≤ (42582929028713/100000000000000 : ℝ)^6213
        have hw : |(5262019407/10000000000 : ℝ)|=(5262019407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069125691/2000000000 : ℝ)*x 0 + (657752427/1250000000 : ℝ)*x 1 + (-1135524127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069125691/2000000000 : ℝ)^8261 ≤ (2717807146529/6250000000000 : ℝ)^6213 := by
    have hnat : (1069125691 : ℕ)^8261*6250000000000^6213 ≤ 2717807146529^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069125691 2000000000 2717807146529 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657752427/1250000000 : ℝ)^8261 ≤ (42582929125553/100000000000000 : ℝ)^6213 := by
    have hnat : (657752427 : ℕ)^8261*100000000000000^6213 ≤ 42582929125553^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657752427 1250000000 42582929125553 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135524127/5000000000 : ℝ)^8261 ≤ (1393215651777/10000000000000 : ℝ)^6213 := by
    have hnat : (1135524127 : ℕ)^8261*10000000000000^6213 ≤ 1393215651777^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135524127 5000000000 1393215651777 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069125691/2000000000 : ℝ), (657752427/1250000000 : ℝ), (-1135524127/5000000000 : ℝ)] ![(2717807146529/6250000000000 : ℝ), (42582929125553/100000000000000 : ℝ), (1393215651777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069125691/2000000000 : ℝ)|^8261 ≤ (2717807146529/6250000000000 : ℝ)^6213
        have hw : |(1069125691/2000000000 : ℝ)|=(1069125691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657752427/1250000000 : ℝ)|^8261 ≤ (42582929125553/100000000000000 : ℝ)^6213
        have hw : |(657752427/1250000000 : ℝ)|=(657752427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135524127/5000000000 : ℝ)|^8261 ≤ (1393215651777/10000000000000 : ℝ)^6213
        have hw : |(-1135524127/5000000000 : ℝ)|=(1135524127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375072277/10000000000 : ℝ)*x 0 + (530603513/1250000000 : ℝ)*x 1 + (2254682657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375072277/10000000000 : ℝ)^8261 ≤ (33315219960417/100000000000000 : ℝ)^6213 := by
    have hnat : (4375072277 : ℕ)^8261*100000000000000^6213 ≤ 33315219960417^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375072277 10000000000 33315219960417 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530603513/1250000000 : ℝ)^8261 ≤ (32003030669629/100000000000000 : ℝ)^6213 := by
    have hnat : (530603513 : ℕ)^8261*100000000000000^6213 ≤ 32003030669629^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530603513 1250000000 32003030669629 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254682657/5000000000 : ℝ)^8261 ≤ (34681749359989/100000000000000 : ℝ)^6213 := by
    have hnat : (2254682657 : ℕ)^8261*100000000000000^6213 ≤ 34681749359989^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254682657 5000000000 34681749359989 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375072277/10000000000 : ℝ), (530603513/1250000000 : ℝ), (2254682657/5000000000 : ℝ)] ![(33315219960417/100000000000000 : ℝ), (32003030669629/100000000000000 : ℝ), (34681749359989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375072277/10000000000 : ℝ)|^8261 ≤ (33315219960417/100000000000000 : ℝ)^6213
        have hw : |(4375072277/10000000000 : ℝ)|=(4375072277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530603513/1250000000 : ℝ)|^8261 ≤ (32003030669629/100000000000000 : ℝ)^6213
        have hw : |(530603513/1250000000 : ℝ)|=(530603513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254682657/5000000000 : ℝ)|^8261 ≤ (34681749359989/100000000000000 : ℝ)^6213
        have hw : |(2254682657/5000000000 : ℝ)|=(2254682657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101279709/5000000000 : ℝ)*x 0 + (5262370571/10000000000 : ℝ)*x 1 + (215863637/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101279709/5000000000 : ℝ)^8261 ≤ (418009314029/3125000000000 : ℝ)^6213 := by
    have hnat : (1101279709 : ℕ)^8261*3125000000000^6213 ≤ 418009314029^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101279709 5000000000 418009314029 3125000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262370571/10000000000 : ℝ)^8261 ≤ (4258670761303/10000000000000 : ℝ)^6213 := by
    have hnat : (5262370571 : ℕ)^8261*10000000000000^6213 ≤ 4258670761303^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262370571 10000000000 4258670761303 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215863637/400000000 : ℝ)^8261 ≤ (44036994323717/100000000000000 : ℝ)^6213 := by
    have hnat : (215863637 : ℕ)^8261*100000000000000^6213 ≤ 44036994323717^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215863637 400000000 44036994323717 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101279709/5000000000 : ℝ), (5262370571/10000000000 : ℝ), (215863637/400000000 : ℝ)] ![(418009314029/3125000000000 : ℝ), (4258670761303/10000000000000 : ℝ), (44036994323717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101279709/5000000000 : ℝ)|^8261 ≤ (418009314029/3125000000000 : ℝ)^6213
        have hw : |(-1101279709/5000000000 : ℝ)|=(1101279709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262370571/10000000000 : ℝ)|^8261 ≤ (4258670761303/10000000000000 : ℝ)^6213
        have hw : |(5262370571/10000000000 : ℝ)|=(5262370571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215863637/400000000 : ℝ)|^8261 ≤ (44036994323717/100000000000000 : ℝ)^6213
        have hw : |(215863637/400000000 : ℝ)|=(215863637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655819421/5000000000 : ℝ)*x 0 + (-1068238373/5000000000 : ℝ)*x 1 + (1079318189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655819421/5000000000 : ℝ)^8261 ≤ (43117664750007/100000000000000 : ℝ)^6213 := by
    have hnat : (2655819421 : ℕ)^8261*100000000000000^6213 ≤ 43117664750007^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655819421 5000000000 43117664750007 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068238373/5000000000 : ℝ)^8261 ≤ (12845340697237/100000000000000 : ℝ)^6213 := by
    have hnat : (1068238373 : ℕ)^8261*100000000000000^6213 ≤ 12845340697237^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068238373 5000000000 12845340697237 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079318189/2000000000 : ℝ)^8261 ≤ (44036994540717/100000000000000 : ℝ)^6213 := by
    have hnat : (1079318189 : ℕ)^8261*100000000000000^6213 ≤ 44036994540717^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079318189 2000000000 44036994540717 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655819421/5000000000 : ℝ), (-1068238373/5000000000 : ℝ), (1079318189/2000000000 : ℝ)] ![(43117664750007/100000000000000 : ℝ), (12845340697237/100000000000000 : ℝ), (44036994540717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655819421/5000000000 : ℝ)|^8261 ≤ (43117664750007/100000000000000 : ℝ)^6213
        have hw : |(2655819421/5000000000 : ℝ)|=(2655819421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068238373/5000000000 : ℝ)|^8261 ≤ (12845340697237/100000000000000 : ℝ)^6213
        have hw : |(-1068238373/5000000000 : ℝ)|=(1068238373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079318189/2000000000 : ℝ)|^8261 ≤ (44036994540717/100000000000000 : ℝ)^6213
        have hw : |(1079318189/2000000000 : ℝ)|=(1079318189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82994357/156250000 : ℝ)*x 0 + (215863637/400000000 : ℝ)*x 1 + (-534119191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82994357/156250000 : ℝ)^8261 ≤ (2694854050923/6250000000000 : ℝ)^6213 := by
    have hnat : (82994357 : ℕ)^8261*6250000000000^6213 ≤ 2694854050923^6213*156250000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82994357 156250000 2694854050923 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215863637/400000000 : ℝ)^8261 ≤ (44036994323717/100000000000000 : ℝ)^6213 := by
    have hnat : (215863637 : ℕ)^8261*100000000000000^6213 ≤ 44036994323717^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215863637 400000000 44036994323717 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534119191/2500000000 : ℝ)^8261 ≤ (6422670420567/50000000000000 : ℝ)^6213 := by
    have hnat : (534119191 : ℕ)^8261*50000000000000^6213 ≤ 6422670420567^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534119191 2500000000 6422670420567 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82994357/156250000 : ℝ), (215863637/400000000 : ℝ), (-534119191/2500000000 : ℝ)] ![(2694854050923/6250000000000 : ℝ), (44036994323717/100000000000000 : ℝ), (6422670420567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82994357/156250000 : ℝ)|^8261 ≤ (2694854050923/6250000000000 : ℝ)^6213
        have hw : |(82994357/156250000 : ℝ)|=(82994357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215863637/400000000 : ℝ)|^8261 ≤ (44036994323717/100000000000000 : ℝ)^6213
        have hw : |(215863637/400000000 : ℝ)|=(215863637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534119191/2500000000 : ℝ)|^8261 ≤ (6422670420567/50000000000000 : ℝ)^6213
        have hw : |(-534119191/2500000000 : ℝ)|=(534119191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s5_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54688543/125000000 : ℝ)*x 0 + (112716921/250000000 : ℝ)*x 1 + (1061379781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54688543/125000000 : ℝ)^8261 ≤ (33315332984197/100000000000000 : ℝ)^6213 := by
    have hnat : (54688543 : ℕ)^8261*100000000000000^6213 ≤ 33315332984197^6213*125000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54688543 125000000 33315332984197 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112716921/250000000 : ℝ)^8261 ≤ (34674709022811/100000000000000 : ℝ)^6213 := by
    have hnat : (112716921 : ℕ)^8261*100000000000000^6213 ≤ 34674709022811^6213*250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112716921 250000000 34674709022811 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061379781/2500000000 : ℝ)^8261 ≤ (16004978989131/50000000000000 : ℝ)^6213 := by
    have hnat : (1061379781 : ℕ)^8261*50000000000000^6213 ≤ 16004978989131^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061379781 2500000000 16004978989131 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54688543/125000000 : ℝ), (112716921/250000000 : ℝ), (1061379781/2500000000 : ℝ)] ![(33315332984197/100000000000000 : ℝ), (34674709022811/100000000000000 : ℝ), (16004978989131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54688543/125000000 : ℝ)|^8261 ≤ (33315332984197/100000000000000 : ℝ)^6213
        have hw : |(54688543/125000000 : ℝ)|=(54688543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112716921/250000000 : ℝ)|^8261 ≤ (34674709022811/100000000000000 : ℝ)^6213
        have hw : |(112716921/250000000 : ℝ)|=(112716921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061379781/2500000000 : ℝ)|^8261 ≤ (16004978989131/50000000000000 : ℝ)^6213
        have hw : |(1061379781/2500000000 : ℝ)|=(1061379781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5513/50000 : ℝ) ^ (2065/512 : ℝ) ≤ (13736536274223343/100000000000000000000 : ℝ) := by
    have hpowers : (5513/50000 : ℝ)^2065 ≤ (13736536274223343/100000000000000000000 : ℝ)^512 := by
      have hnat : (5513 : ℕ)^2065*100000000000000000000^512 ≤ 13736536274223343^512*50000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5513 50000 13736536274223343 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5513/50000 : ℝ)) (X := (13736536274223343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14243/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (241092021508831/625000000000000000 : ℝ) := by
    have hpowers : (14243/100000 : ℝ)^2065 ≤ (241092021508831/625000000000000000 : ℝ)^512 := by
      have hnat : (14243 : ℕ)^2065*625000000000000000^512 ≤ 241092021508831^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14243 100000 241092021508831 625000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14243/100000 : ℝ)) (X := (241092021508831/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013736536274223343/50000000000000000000 : ℝ) ≤ (5000340551095481/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50013736536274223343/50000000000000000000 : ℝ)^512 ≤ (5000340551095481/5000000000000000 : ℝ)^2065 := by
      have hnat : (50013736536274223343 : ℕ)^512*5000000000000000^2065 ≤ 5000340551095481^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013736536274223343 50000000000000000000 5000340551095481 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340551095481/5000000000000000 : ℝ)) (X := (50013736536274223343/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052311259715636303/100000000000000000000 : ℝ) ≤ (5000648380100417/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (100052311259715636303/100000000000000000000 : ℝ)^512 ≤ (5000648380100417/5000000000000000 : ℝ)^2065 := by
      have hnat : (100052311259715636303 : ℕ)^512*5000000000000000^2065 ≤ 5000648380100417^2065*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052311259715636303 100000000000000000000 5000648380100417 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000648380100417/5000000000000000 : ℝ)) (X := (100052311259715636303/100000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312741092021508831/312500000000000000 : ℝ) ≤ (5000956209105353/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (312741092021508831/312500000000000000 : ℝ)^512 ≤ (5000956209105353/5000000000000000 : ℝ)^2065 := by
      have hnat : (312741092021508831 : ℕ)^512*5000000000000000^2065 ≤ 5000956209105353^2065*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312741092021508831 312500000000000000 5000956209105353 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000956209105353/5000000000000000 : ℝ)) (X := (312741092021508831/312500000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13736536274223343/100000000000000000000 : ℝ) ≤ ((3215861461531462741/3217000000000000000 : ℝ)+2*(38478625617/20106250000000 : ℝ)*(5513/50000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (3215861461531462741/3217000000000000000 : ℝ)+2*(38478625617/20106250000000 : ℝ)*(5513/50000 : ℝ)=(5000340551095481/5000000000000000 : ℝ) by norm_num, show 1+2*(13736536274223343/100000000000000000000 : ℝ)=(50013736536274223343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(241092021508831/625000000000000000 : ℝ)+(13736536274223343/100000000000000000000 : ℝ) ≤ ((3215861461531462741/3217000000000000000 : ℝ)+(38478625617/20106250000000 : ℝ)*((14243/100000 : ℝ)+(5513/50000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (3215861461531462741/3217000000000000000 : ℝ)+(38478625617/20106250000000 : ℝ)*((14243/100000 : ℝ)+(5513/50000 : ℝ))=(5000648380100417/5000000000000000 : ℝ) by norm_num, show 1+(241092021508831/625000000000000000 : ℝ)+(13736536274223343/100000000000000000000 : ℝ)=(100052311259715636303/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(241092021508831/625000000000000000 : ℝ) ≤ ((3215861461531462741/3217000000000000000 : ℝ)+2*(38478625617/20106250000000 : ℝ)*(14243/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (3215861461531462741/3217000000000000000 : ℝ)+2*(38478625617/20106250000000 : ℝ)*(14243/100000 : ℝ)=(5000956209105353/5000000000000000 : ℝ) by norm_num, show 1+2*(241092021508831/625000000000000000 : ℝ)=(312741092021508831/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3215861461531462741/3217000000000000000 : ℝ)*(X 1 0+X 2 0)+(38478625617/20106250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (3215861461531462741/3217000000000000000 : ℝ)) (alpha := (38478625617/20106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3215861461531462741/3217000000000000000 : ℝ)*(X 0 1+X 2 1)+(38478625617/20106250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (3215861461531462741/3217000000000000000 : ℝ)) (alpha := (38478625617/20106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3215861461531462741/3217000000000000000 : ℝ)*(X 0 2+X 1 2)+(38478625617/20106250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (3215861461531462741/3217000000000000000 : ℝ)) (alpha := (38478625617/20106250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440510747/2000000000 : ℝ)*X 0 0+(1349235849/2500000000 : ℝ)*X 0 1+(2631009709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668203557/1250000000 : ℝ)*X 1 0+(-283881033/1250000000 : ℝ)*X 1 1+(5262019407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069125691/2000000000 : ℝ)*X 2 0+(657752427/1250000000 : ℝ)*X 2 1+(-1135524127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375072277/10000000000 : ℝ)*X 0 0+(530603513/1250000000 : ℝ)*X 0 1+(2254682657/5000000000 : ℝ)*X 0 2+(4375072277/10000000000 : ℝ)*X 1 0+(530603513/1250000000 : ℝ)*X 1 1+(2254682657/5000000000 : ℝ)*X 1 2+(4375072277/10000000000 : ℝ)*X 2 0+(530603513/1250000000 : ℝ)*X 2 1+(2254682657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101279709/5000000000 : ℝ)*X 0 0+(5262370571/10000000000 : ℝ)*X 0 1+(215863637/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655819421/5000000000 : ℝ)*X 1 0+(-1068238373/5000000000 : ℝ)*X 1 1+(1079318189/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82994357/156250000 : ℝ)*X 2 0+(215863637/400000000 : ℝ)*X 2 1+(-534119191/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54688543/125000000 : ℝ)*X 0 0+(112716921/250000000 : ℝ)*X 0 1+(1061379781/2500000000 : ℝ)*X 0 2+(54688543/125000000 : ℝ)*X 1 0+(112716921/250000000 : ℝ)*X 1 1+(1061379781/2500000000 : ℝ)*X 1 2+(54688543/125000000 : ℝ)*X 2 0+(112716921/250000000 : ℝ)*X 2 1+(1061379781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17354942080061064910047/8042500000000000000000000000 : ℝ) := by norm_num
    linear_combination (452194523/100000000000000 : ℝ)*(base19) + (13107427/3125000000000 : ℝ)*(base23) + (104809/625000000000 : ℝ)*(lower2) + (46363101/100000000000000 : ℝ)*(upper3) + (7633493/20000000000000 : ℝ)*(upper5) + (5595901728341509/100000000000000 : ℝ)*(major0) + (5595901728341509/100000000000000 : ℝ)*(major1) + (5595901728341509/100000000000000 : ℝ)*(major2) + (7411592820229123/100000000000000 : ℝ)*(sp0) + (1482320847557011/20000000000000 : ℝ)*(sp1) + (7411604270541913/100000000000000 : ℝ)*(sp2) + (3780192445630469/100000000000000 : ℝ)*(sp3) + (5934875227/50000000000000 : ℝ)*(sp4) + (1249828567/20000000000000 : ℝ)*(sp7) + (472524836846663/12500000000000 : ℝ)*(f.failure) + (3705802344989789/50000000000000 : ℝ)*(f.sum) + (1369381113839/2010625000000000000000000000 : ℝ)*base66 + (1366954369534903831/321700000000000000000000000000000 : ℝ)*base68 + (4733887946536696169/321700000000000000000000000000000 : ℝ)*base69 + (3068693412402403831/321700000000000000000000000000000 : ℝ)*base72 + (1970694228761/2010625000000000000000000000 : ℝ)*base73 + (1002675582380996169/321700000000000000000000000000000 : ℝ)*base75 + (797043804528096169/321700000000000000000000000000000 : ℝ)*base77 + (795155738827103831/321700000000000000000000000000000 : ℝ)*base80 + (3567192824249/2010625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1842861/1250000000000000000000 : ℝ)*base89 + (1842861/1250000000000000000000 : ℝ)*base91 + (1842861/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17759528093265229235157/4021250000000000000000000000 : ℝ) := by norm_num
    linear_combination (801093007/100000000000000 : ℝ)*(base19) + (898793779/100000000000000 : ℝ)*(base23) + (52669977/50000000000000 : ℝ)*(upper3) + (4121761/10000000000000 : ℝ)*(lower4) + (21624429/25000000000000 : ℝ)*(upper5) + (703152237990481/12500000000000 : ℝ)*(major0) + (703152237990481/12500000000000 : ℝ)*(major1) + (703152237990481/12500000000000 : ℝ)*(major2) + (4136636889/20000000000000 : ℝ)*(sp1) + (22509409207/100000000000000 : ℝ)*(sp2) + (7450433013959157/100000000000000 : ℝ)*(sp4) + (1490082305936341/20000000000000 : ℝ)*(sp5) + (7450409605756171/100000000000000 : ℝ)*(sp6) + (3800002646674537/100000000000000 : ℝ)*(sp7) + (3800002646674537/100000000000000 : ℝ)*(f.failure) + (7450433013959157/100000000000000 : ℝ)*(f.sum) + (28440831876067/8042500000000000000000000000 : ℝ)*base66 + (306756613173499079/40212500000000000000000000000000 : ℝ)*base68 + (690062842518225921/40212500000000000000000000000000 : ℝ)*base69 + (164465811211136579/40212500000000000000000000000000 : ℝ)*base72 + (8220064847247/8042500000000000000000000000 : ℝ)*base74 + (1450125935456288421/40212500000000000000000000000000 : ℝ)*base75 + (60154632490475921/40212500000000000000000000000000 : ℝ)*base77 + (311250064084499079/40212500000000000000000000000000 : ℝ)*base80 + (31582889370173/8042500000000000000000000000 : ℝ)*base81 + (12566461/10000000000000000000000 : ℝ)*base90 + (12566461/10000000000000000000000 : ℝ)*base92 + (12566461/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1068_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1068_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1068_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1068_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
