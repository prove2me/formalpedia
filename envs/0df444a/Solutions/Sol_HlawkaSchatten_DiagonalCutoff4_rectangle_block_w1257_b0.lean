-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:18.568414+00:00
-- url     : https://prove2.me/submissions/b1e11b0b-94ae-4e80-933d-7936ff9e31cd

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
theorem support_rectangle_w1257_s0_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-371188109/2000000000 : ℝ)*x 0 + (3014065423/5000000000 : ℝ)*x 1 + (299677637/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371188109/2000000000 : ℝ)^4225 ≤ (10828733839463/100000000000000 : ℝ)^3201 := by
    have hnat : (371188109 : ℕ)^4225*100000000000000^3201 ≤ 10828733839463^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371188109 2000000000 10828733839463 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014065423/5000000000 : ℝ)^4225 ≤ (5126997432119/10000000000000 : ℝ)^3201 := by
    have hnat : (3014065423 : ℕ)^4225*10000000000000^3201 ≤ 5126997432119^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014065423 5000000000 5126997432119 10000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299677637/625000000 : ℝ)^4225 ≤ (37901291822653/100000000000000 : ℝ)^3201 := by
    have hnat : (299677637 : ℕ)^4225*100000000000000^3201 ≤ 37901291822653^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299677637 625000000 37901291822653 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371188109/2000000000 : ℝ), (3014065423/5000000000 : ℝ), (299677637/625000000 : ℝ)] ![(10828733839463/100000000000000 : ℝ), (5126997432119/10000000000000 : ℝ), (37901291822653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371188109/2000000000 : ℝ)|^4225 ≤ (10828733839463/100000000000000 : ℝ)^3201
        have hw : |(-371188109/2000000000 : ℝ)|=(371188109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3014065423/5000000000 : ℝ)|^4225 ≤ (5126997432119/10000000000000 : ℝ)^3201
        have hw : |(3014065423/5000000000 : ℝ)|=(3014065423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299677637/625000000 : ℝ)|^4225 ≤ (37901291822653/100000000000000 : ℝ)^3201
        have hw : |(299677637/625000000 : ℝ)|=(299677637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755157227/5000000000 : ℝ)*x 0 + (-2560580431/10000000000 : ℝ)*x 1 + (4794842137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755157227/5000000000 : ℝ)^4225 ≤ (45538497785107/100000000000000 : ℝ)^3201 := by
    have hnat : (2755157227 : ℕ)^4225*100000000000000^3201 ≤ 45538497785107^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755157227 5000000000 45538497785107 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560580431/10000000000 : ℝ)^4225 ≤ (8280105478361/50000000000000 : ℝ)^3201 := by
    have hnat : (2560580431 : ℕ)^4225*50000000000000^3201 ≤ 8280105478361^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560580431 10000000000 8280105478361 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794842137/10000000000 : ℝ)^4225 ≤ (37901291248823/100000000000000 : ℝ)^3201 := by
    have hnat : (4794842137 : ℕ)^4225*100000000000000^3201 ≤ 37901291248823^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794842137 10000000000 37901291248823 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755157227/5000000000 : ℝ), (-2560580431/10000000000 : ℝ), (4794842137/10000000000 : ℝ)] ![(45538497785107/100000000000000 : ℝ), (8280105478361/50000000000000 : ℝ), (37901291248823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755157227/5000000000 : ℝ)|^4225 ≤ (45538497785107/100000000000000 : ℝ)^3201
        have hw : |(2755157227/5000000000 : ℝ)|=(2755157227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2560580431/10000000000 : ℝ)|^4225 ≤ (8280105478361/50000000000000 : ℝ)^3201
        have hw : |(-2560580431/10000000000 : ℝ)|=(2560580431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794842137/10000000000 : ℝ)|^4225 ≤ (37901291248823/100000000000000 : ℝ)^3201
        have hw : |(4794842137/10000000000 : ℝ)|=(4794842137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5510314471/10000000000 : ℝ)*x 0 + (4794842163/10000000000 : ℝ)*x 1 + (-2560580377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510314471/10000000000 : ℝ)^4225 ≤ (45538497970543/100000000000000 : ℝ)^3201 := by
    have hnat : (5510314471 : ℕ)^4225*100000000000000^3201 ≤ 45538497970543^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510314471 10000000000 45538497970543 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794842163/10000000000 : ℝ)^4225 ≤ (4737661440011/12500000000000 : ℝ)^3201 := by
    have hnat : (4794842163 : ℕ)^4225*12500000000000^3201 ≤ 4737661440011^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794842163 10000000000 4737661440011 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560580377/10000000000 : ℝ)^4225 ≤ (16560210495763/100000000000000 : ℝ)^3201 := by
    have hnat : (2560580377 : ℕ)^4225*100000000000000^3201 ≤ 16560210495763^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560580377 10000000000 16560210495763 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510314471/10000000000 : ℝ), (4794842163/10000000000 : ℝ), (-2560580377/10000000000 : ℝ)] ![(45538497970543/100000000000000 : ℝ), (4737661440011/12500000000000 : ℝ), (16560210495763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510314471/10000000000 : ℝ)|^4225 ≤ (45538497970543/100000000000000 : ℝ)^3201
        have hw : |(5510314471/10000000000 : ℝ)|=(5510314471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794842163/10000000000 : ℝ)|^4225 ≤ (4737661440011/12500000000000 : ℝ)^3201
        have hw : |(4794842163/10000000000 : ℝ)|=(4794842163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2560580377/10000000000 : ℝ)|^4225 ≤ (16560210495763/100000000000000 : ℝ)^3201
        have hw : |(-2560580377/10000000000 : ℝ)|=(2560580377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191846011/10000000000 : ℝ)*x 0 + (194771107/625000000 : ℝ)*x 1 + (5625398927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191846011/10000000000 : ℝ)^4225 ≤ (31740427402151/100000000000000 : ℝ)^3201 := by
    have hnat : (4191846011 : ℕ)^4225*100000000000000^3201 ≤ 31740427402151^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191846011 10000000000 31740427402151 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194771107/625000000 : ℝ)^4225 ≤ (21461564599493/100000000000000 : ℝ)^3201 := by
    have hnat : (194771107 : ℕ)^4225*100000000000000^3201 ≤ 21461564599493^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194771107 625000000 21461564599493 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5625398927/10000000000 : ℝ)^4225 ≤ (23399003992993/50000000000000 : ℝ)^3201 := by
    have hnat : (5625398927 : ℕ)^4225*50000000000000^3201 ≤ 23399003992993^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625398927 10000000000 23399003992993 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191846011/10000000000 : ℝ), (194771107/625000000 : ℝ), (5625398927/10000000000 : ℝ)] ![(31740427402151/100000000000000 : ℝ), (21461564599493/100000000000000 : ℝ), (23399003992993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191846011/10000000000 : ℝ)|^4225 ≤ (31740427402151/100000000000000 : ℝ)^3201
        have hw : |(4191846011/10000000000 : ℝ)|=(4191846011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194771107/625000000 : ℝ)|^4225 ≤ (21461564599493/100000000000000 : ℝ)^3201
        have hw : |(194771107/625000000 : ℝ)|=(194771107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5625398927/10000000000 : ℝ)|^4225 ≤ (23399003992993/50000000000000 : ℝ)^3201
        have hw : |(5625398927/10000000000 : ℝ)|=(5625398927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860755513/10000000000 : ℝ)*x 0 + (60332401/125000000 : ℝ)*x 1 + (5995258309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860755513/10000000000 : ℝ)^4225 ≤ (2173165985931/20000000000000 : ℝ)^3201 := by
    have hnat : (1860755513 : ℕ)^4225*20000000000000^3201 ≤ 2173165985931^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860755513 10000000000 2173165985931 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60332401/125000000 : ℝ)^4225 ≤ (7646579503041/20000000000000 : ℝ)^3201 := by
    have hnat : (60332401 : ℕ)^4225*20000000000000^3201 ≤ 7646579503041^3201*125000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60332401 125000000 7646579503041 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5995258309/10000000000 : ℝ)^4225 ≤ (25450636264623/50000000000000 : ℝ)^3201 := by
    have hnat : (5995258309 : ℕ)^4225*50000000000000^3201 ≤ 25450636264623^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995258309 10000000000 25450636264623 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860755513/10000000000 : ℝ), (60332401/125000000 : ℝ), (5995258309/10000000000 : ℝ)] ![(2173165985931/20000000000000 : ℝ), (7646579503041/20000000000000 : ℝ), (25450636264623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860755513/10000000000 : ℝ)|^4225 ≤ (2173165985931/20000000000000 : ℝ)^3201
        have hw : |(-1860755513/10000000000 : ℝ)|=(1860755513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60332401/125000000 : ℝ)|^4225 ≤ (7646579503041/20000000000000 : ℝ)^3201
        have hw : |(60332401/125000000 : ℝ)|=(60332401/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5995258309/10000000000 : ℝ)|^4225 ≤ (25450636264623/50000000000000 : ℝ)^3201
        have hw : |(5995258309/10000000000 : ℝ)|=(5995258309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517469153/1000000000 : ℝ)*x 0 + (-1360161979/10000000000 : ℝ)*x 1 + (2997630349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517469153/1000000000 : ℝ)^4225 ≤ (41913709382961/100000000000000 : ℝ)^3201 := by
    have hnat : (517469153 : ℕ)^4225*100000000000000^3201 ≤ 41913709382961^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517469153 1000000000 41913709382961 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360161979/10000000000 : ℝ)^4225 ≤ (7184991297021/100000000000000 : ℝ)^3201 := by
    have hnat : (1360161979 : ℕ)^4225*100000000000000^3201 ≤ 7184991297021^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360161979 10000000000 7184991297021 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2997630349/5000000000 : ℝ)^4225 ≤ (50901299301069/100000000000000 : ℝ)^3201 := by
    have hnat : (2997630349 : ℕ)^4225*100000000000000^3201 ≤ 50901299301069^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997630349 5000000000 50901299301069 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517469153/1000000000 : ℝ), (-1360161979/10000000000 : ℝ), (2997630349/5000000000 : ℝ)] ![(41913709382961/100000000000000 : ℝ), (7184991297021/100000000000000 : ℝ), (50901299301069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517469153/1000000000 : ℝ)|^4225 ≤ (41913709382961/100000000000000 : ℝ)^3201
        have hw : |(517469153/1000000000 : ℝ)|=(517469153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1360161979/10000000000 : ℝ)|^4225 ≤ (7184991297021/100000000000000 : ℝ)^3201
        have hw : |(-1360161979/10000000000 : ℝ)|=(1360161979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2997630349/5000000000 : ℝ)|^4225 ≤ (50901299301069/100000000000000 : ℝ)^3201
        have hw : |(2997630349/5000000000 : ℝ)|=(2997630349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293673139/2500000000 : ℝ)*x 0 + (5995258731/10000000000 : ℝ)*x 1 + (-85010223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293673139/2500000000 : ℝ)^4225 ≤ (5239215043973/12500000000000 : ℝ)^3201 := by
    have hnat : (1293673139 : ℕ)^4225*12500000000000^3201 ≤ 5239215043973^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293673139 2500000000 5239215043973 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5995258731/10000000000 : ℝ)^4225 ≤ (50901277258299/100000000000000 : ℝ)^3201 := by
    have hnat : (5995258731 : ℕ)^4225*100000000000000^3201 ≤ 50901277258299^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995258731 10000000000 50901277258299 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85010223/625000000 : ℝ)^4225 ≤ (3592501188011/50000000000000 : ℝ)^3201 := by
    have hnat : (85010223 : ℕ)^4225*50000000000000^3201 ≤ 3592501188011^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85010223 625000000 3592501188011 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293673139/2500000000 : ℝ), (5995258731/10000000000 : ℝ), (-85010223/625000000 : ℝ)] ![(5239215043973/12500000000000 : ℝ), (50901277258299/100000000000000 : ℝ), (3592501188011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293673139/2500000000 : ℝ)|^4225 ≤ (5239215043973/12500000000000 : ℝ)^3201
        have hw : |(1293673139/2500000000 : ℝ)|=(1293673139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5995258731/10000000000 : ℝ)|^4225 ≤ (50901277258299/100000000000000 : ℝ)^3201
        have hw : |(5995258731/10000000000 : ℝ)|=(5995258731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85010223/625000000 : ℝ)|^4225 ≤ (3592501188011/50000000000000 : ℝ)^3201
        have hw : |(-85010223/625000000 : ℝ)|=(85010223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s0_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201643947/10000000000 : ℝ)*x 0 + (1112162211/2000000000 : ℝ)*x 1 + (198950581/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201643947/10000000000 : ℝ)^4225 ≤ (6367677325333/20000000000000 : ℝ)^3201 := by
    have hnat : (4201643947 : ℕ)^4225*20000000000000^3201 ≤ 6367677325333^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201643947 10000000000 6367677325333 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112162211/2000000000 : ℝ)^4225 ≤ (23045059082209/50000000000000 : ℝ)^3201 := by
    have hnat : (1112162211 : ℕ)^4225*50000000000000^3201 ≤ 23045059082209^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112162211 2000000000 23045059082209 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198950581/625000000 : ℝ)^4225 ≤ (22071495190093/100000000000000 : ℝ)^3201 := by
    have hnat : (198950581 : ℕ)^4225*100000000000000^3201 ≤ 22071495190093^3201*625000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198950581 625000000 22071495190093 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201643947/10000000000 : ℝ), (1112162211/2000000000 : ℝ), (198950581/625000000 : ℝ)] ![(6367677325333/20000000000000 : ℝ), (23045059082209/50000000000000 : ℝ), (22071495190093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201643947/10000000000 : ℝ)|^4225 ≤ (6367677325333/20000000000000 : ℝ)^3201
        have hw : |(4201643947/10000000000 : ℝ)|=(4201643947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112162211/2000000000 : ℝ)|^4225 ≤ (23045059082209/50000000000000 : ℝ)^3201
        have hw : |(1112162211/2000000000 : ℝ)|=(1112162211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198950581/625000000 : ℝ)|^4225 ≤ (22071495190093/100000000000000 : ℝ)^3201
        have hw : |(198950581/625000000 : ℝ)|=(198950581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (439/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1369/5000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8449/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8449 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8449*1^2048 ≤ 0^2048*1^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8449/2048 : ℝ) ≤ (2281934411660682247/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8449 ≤ (2281934411660682247/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8449*100000000000000000000^2048 ≤ 2281934411660682247^2048*5^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2281934411660682247 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2281934411660682247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8449 := by
      have hnat : (1 : ℕ)^2048*1^8449 ≤ 1^8449*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102281934411660682247/100000000000000000000 : ℝ) ≤ (502742062033637/500000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (102281934411660682247/100000000000000000000 : ℝ)^2048 ≤ (502742062033637/500000000000000 : ℝ)^8449 := by
      have hnat : (102281934411660682247 : ℕ)^2048*500000000000000^8449 ≤ 502742062033637^8449*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102281934411660682247 100000000000000000000 502742062033637 500000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502742062033637/500000000000000 : ℝ)) (X := (102281934411660682247/100000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52281934411660682247/50000000000000000000 : ℝ) ≤ (252742062033637/250000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (52281934411660682247/50000000000000000000 : ℝ)^2048 ≤ (252742062033637/250000000000000 : ℝ)^8449 := by
      have hnat : (52281934411660682247 : ℕ)^2048*250000000000000^8449 ≤ 252742062033637^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52281934411660682247 50000000000000000000 252742062033637 250000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252742062033637/250000000000000 : ℝ)) (X := (52281934411660682247/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2742062033637/200000000000000 : ℝ)*(0 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2742062033637/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2281934411660682247/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2742062033637/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (1 : ℝ)+(2742062033637/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502742062033637/500000000000000 : ℝ) by norm_num, show 1+(2281934411660682247/100000000000000000000 : ℝ)+(0 : ℝ)=(102281934411660682247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2281934411660682247/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2742062033637/200000000000000 : ℝ)*(2/5 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2742062033637/200000000000000 : ℝ)*(2/5 : ℝ)=(252742062033637/250000000000000 : ℝ) by norm_num, show 1+2*(2281934411660682247/100000000000000000000 : ℝ)=(52281934411660682247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2742062033637/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2742062033637/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2742062033637/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2742062033637/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2742062033637/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2742062033637/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-371188109/2000000000 : ℝ)*X 0 0+(3014065423/5000000000 : ℝ)*X 0 1+(299677637/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755157227/5000000000 : ℝ)*X 1 0+(-2560580431/10000000000 : ℝ)*X 1 1+(4794842137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510314471/10000000000 : ℝ)*X 2 0+(4794842163/10000000000 : ℝ)*X 2 1+(-2560580377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4191846011/10000000000 : ℝ)*X 0 0+(194771107/625000000 : ℝ)*X 0 1+(5625398927/10000000000 : ℝ)*X 0 2+(4191846011/10000000000 : ℝ)*X 1 0+(194771107/625000000 : ℝ)*X 1 1+(5625398927/10000000000 : ℝ)*X 1 2+(4191846011/10000000000 : ℝ)*X 2 0+(194771107/625000000 : ℝ)*X 2 1+(5625398927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1860755513/10000000000 : ℝ)*X 0 0+(60332401/125000000 : ℝ)*X 0 1+(5995258309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517469153/1000000000 : ℝ)*X 1 0+(-1360161979/10000000000 : ℝ)*X 1 1+(2997630349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293673139/2500000000 : ℝ)*X 2 0+(5995258731/10000000000 : ℝ)*X 2 1+(-85010223/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201643947/10000000000 : ℝ)*X 0 0+(1112162211/2000000000 : ℝ)*X 0 1+(198950581/625000000 : ℝ)*X 0 2+(4201643947/10000000000 : ℝ)*X 1 0+(1112162211/2000000000 : ℝ)*X 1 1+(198950581/625000000 : ℝ)*X 1 2+(4201643947/10000000000 : ℝ)*X 2 0+(1112162211/2000000000 : ℝ)*X 2 1+(198950581/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20116516137839339840871/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29373209/100000000000000 : ℝ)*(base1) + (130744189/25000000000000 : ℝ)*(base19) + (243594547/50000000000000 : ℝ)*(base23) + (38289211/100000000000000 : ℝ)*(base24) + (56790871/50000000000000 : ℝ)*(upper3) + (604700021817639/100000000000000 : ℝ)*(major0) + (604700021817639/100000000000000 : ℝ)*(major1) + (604700021817639/100000000000000 : ℝ)*(major2) + (162168385747259/20000000000000 : ℝ)*(sp0) + (405421271708693/50000000000000 : ℝ)*(sp1) + (405421270457919/50000000000000 : ℝ)*(sp2) + (398555977387527/100000000000000 : ℝ)*(sp3) + (1167031057/100000000000000 : ℝ)*(sp4) + (45171267/5000000000000 : ℝ)*(sp7) + (99639227546519/25000000000000 : ℝ)*(f.failure) + (810843066394143/100000000000000 : ℝ)*(f.sum) + (23715760313043/10000000000000000000000000000 : ℝ)*base65 + (9722776843043/20000000000000000000000000000 : ℝ)*base67 + (127074610516957/20000000000000000000000000000 : ℝ)*base70 + (68181117503043/20000000000000000000000000000 : ℝ)*base71 + (1356712343043/10000000000000000000000000000 : ℝ)*base73 + (102462736903043/20000000000000000000000000000 : ℝ)*base75 + (73694771576957/20000000000000000000000000000 : ℝ)*base78 + (33425092436957/20000000000000000000000000000 : ℝ)*base80 + (54410834506957/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3348909/1250000000000000000000 : ℝ)*base90 + (3348909/1250000000000000000000 : ℝ)*base92 + (3348909/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21668179263587068654809/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25097599/12500000000000 : ℝ)*(base1) + (953054689/100000000000000 : ℝ)*(base19) + (219117419/20000000000000 : ℝ)*(base23) + (212343613/100000000000000 : ℝ)*(upper3) + (638134112055827/100000000000000 : ℝ)*(major0) + (638134112055827/100000000000000 : ℝ)*(major1) + (638134112055827/100000000000000 : ℝ)*(major2) + (105537099/5000000000000 : ℝ)*(sp1) + (105783729/6250000000000 : ℝ)*(sp2) + (139488883/50000000000000 : ℝ)*(sp3) + (171135001942071/20000000000000 : ℝ)*(sp4) + (427835872566447/50000000000000 : ℝ)*(sp5) + (213918005200701/25000000000000 : ℝ)*(sp6) + (210296395484499/50000000000000 : ℝ)*(sp7) + (420593270727557/100000000000000 : ℝ)*(f.failure) + (855674808929563/100000000000000 : ℝ)*(f.sum) + (35455401682799/10000000000000000000000000000 : ℝ)*base65 + (106763042212799/20000000000000000000000000000 : ℝ)*base67 + (16387452152799/20000000000000000000000000000 : ℝ)*base69 + (169404230412799/20000000000000000000000000000 : ℝ)*base71 + (25854959092799/10000000000000000000000000000 : ℝ)*base73 + (81849020612799/20000000000000000000000000000 : ℝ)*base75 + (91031469852799/20000000000000000000000000000 : ℝ)*base77 + (201356111092799/20000000000000000000000000000 : ℝ)*base79 + (24732050952799/10000000000000000000000000000 : ℝ)*base81 + (19085273/5000000000000000000000 : ℝ)*base89 + (19085273/5000000000000000000000 : ℝ)*base91 + (19085273/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1257_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1369/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s1_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-513065067/2500000000 : ℝ)*x 0 + (5671854317/10000000000 : ℝ)*x 1 + (1256362869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513065067/2500000000 : ℝ)^4225 ≤ (6182805388501/50000000000000 : ℝ)^3201 := by
    have hnat : (513065067 : ℕ)^4225*50000000000000^3201 ≤ 6182805388501^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513065067 2500000000 6182805388501 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671854317/10000000000 : ℝ)^4225 ≤ (1478399239219/3125000000000 : ℝ)^3201 := by
    have hnat : (5671854317 : ℕ)^4225*3125000000000^3201 ≤ 1478399239219^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671854317 10000000000 1478399239219 3125000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256362869/2500000000 : ℝ)^4225 ≤ (40325613560419/100000000000000 : ℝ)^3201 := by
    have hnat : (1256362869 : ℕ)^4225*100000000000000^3201 ≤ 40325613560419^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256362869 2500000000 40325613560419 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513065067/2500000000 : ℝ), (5671854317/10000000000 : ℝ), (1256362869/2500000000 : ℝ)] ![(6182805388501/50000000000000 : ℝ), (1478399239219/3125000000000 : ℝ), (40325613560419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513065067/2500000000 : ℝ)|^4225 ≤ (6182805388501/50000000000000 : ℝ)^3201
        have hw : |(-513065067/2500000000 : ℝ)|=(513065067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671854317/10000000000 : ℝ)|^4225 ≤ (1478399239219/3125000000000 : ℝ)^3201
        have hw : |(5671854317/10000000000 : ℝ)|=(5671854317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256362869/2500000000 : ℝ)|^4225 ≤ (40325613560419/100000000000000 : ℝ)^3201
        have hw : |(1256362869/2500000000 : ℝ)|=(1256362869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706421897/5000000000 : ℝ)*x 0 + (-2399123041/10000000000 : ℝ)*x 1 + (1256362947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706421897/5000000000 : ℝ)^4225 ≤ (44478312467323/100000000000000 : ℝ)^3201 := by
    have hnat : (2706421897 : ℕ)^4225*100000000000000^3201 ≤ 44478312467323^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706421897 5000000000 44478312467323 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399123041/10000000000 : ℝ)^4225 ≤ (15196070649597/100000000000000 : ℝ)^3201 := by
    have hnat : (2399123041 : ℕ)^4225*100000000000000^3201 ≤ 15196070649597^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399123041 10000000000 15196070649597 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256362947/2500000000 : ℝ)^4225 ≤ (40325616864887/100000000000000 : ℝ)^3201 := by
    have hnat : (1256362947 : ℕ)^4225*100000000000000^3201 ≤ 40325616864887^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256362947 2500000000 40325616864887 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706421897/5000000000 : ℝ), (-2399123041/10000000000 : ℝ), (1256362947/2500000000 : ℝ)] ![(44478312467323/100000000000000 : ℝ), (15196070649597/100000000000000 : ℝ), (40325616864887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706421897/5000000000 : ℝ)|^4225 ≤ (44478312467323/100000000000000 : ℝ)^3201
        have hw : |(2706421897/5000000000 : ℝ)|=(2706421897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2399123041/10000000000 : ℝ)|^4225 ≤ (15196070649597/100000000000000 : ℝ)^3201
        have hw : |(-2399123041/10000000000 : ℝ)|=(2399123041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256362947/2500000000 : ℝ)|^4225 ≤ (40325616864887/100000000000000 : ℝ)^3201
        have hw : |(1256362947/2500000000 : ℝ)|=(1256362947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353211021/2500000000 : ℝ)*x 0 + (2512725793/5000000000 : ℝ)*x 1 + (-1199561461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353211021/2500000000 : ℝ)^4225 ≤ (44478315612621/100000000000000 : ℝ)^3201 := by
    have hnat : (1353211021 : ℕ)^4225*100000000000000^3201 ≤ 44478315612621^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353211021 2500000000 44478315612621 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512725793/5000000000 : ℝ)^4225 ≤ (2520350920341/6250000000000 : ℝ)^3201 := by
    have hnat : (2512725793 : ℕ)^4225*6250000000000^3201 ≤ 2520350920341^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512725793 5000000000 2520350920341 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199561461/5000000000 : ℝ)^4225 ≤ (7598034827363/50000000000000 : ℝ)^3201 := by
    have hnat : (1199561461 : ℕ)^4225*50000000000000^3201 ≤ 7598034827363^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199561461 5000000000 7598034827363 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353211021/2500000000 : ℝ), (2512725793/5000000000 : ℝ), (-1199561461/5000000000 : ℝ)] ![(44478315612621/100000000000000 : ℝ), (2520350920341/6250000000000 : ℝ), (7598034827363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353211021/2500000000 : ℝ)|^4225 ≤ (44478315612621/100000000000000 : ℝ)^3201
        have hw : |(1353211021/2500000000 : ℝ)|=(1353211021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512725793/5000000000 : ℝ)|^4225 ≤ (2520350920341/6250000000000 : ℝ)^3201
        have hw : |(2512725793/5000000000 : ℝ)|=(2512725793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199561461/5000000000 : ℝ)|^4225 ≤ (7598034827363/50000000000000 : ℝ)^3201
        have hw : |(-1199561461/5000000000 : ℝ)|=(1199561461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307552143/10000000000 : ℝ)*x 0 + (924538329/2500000000 : ℝ)*x 1 + (2506613309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307552143/10000000000 : ℝ)^4225 ≤ (16450946386501/50000000000000 : ℝ)^3201 := by
    have hnat : (4307552143 : ℕ)^4225*50000000000000^3201 ≤ 16450946386501^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307552143 10000000000 16450946386501 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924538329/2500000000 : ℝ)^4225 ≤ (26901919684289/100000000000000 : ℝ)^3201 := by
    have hnat : (924538329 : ℕ)^4225*100000000000000^3201 ≤ 26901919684289^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924538329 2500000000 26901919684289 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506613309/5000000000 : ℝ)^4225 ≤ (20098093761411/50000000000000 : ℝ)^3201 := by
    have hnat : (2506613309 : ℕ)^4225*50000000000000^3201 ≤ 20098093761411^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506613309 5000000000 20098093761411 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307552143/10000000000 : ℝ), (924538329/2500000000 : ℝ), (2506613309/5000000000 : ℝ)] ![(16450946386501/50000000000000 : ℝ), (26901919684289/100000000000000 : ℝ), (20098093761411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307552143/10000000000 : ℝ)|^4225 ≤ (16450946386501/50000000000000 : ℝ)^3201
        have hw : |(4307552143/10000000000 : ℝ)|=(4307552143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924538329/2500000000 : ℝ)|^4225 ≤ (26901919684289/100000000000000 : ℝ)^3201
        have hw : |(924538329/2500000000 : ℝ)|=(924538329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506613309/5000000000 : ℝ)|^4225 ≤ (20098093761411/50000000000000 : ℝ)^3201
        have hw : |(2506613309/5000000000 : ℝ)|=(2506613309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026459423/5000000000 : ℝ)*x 0 + (2516946329/5000000000 : ℝ)*x 1 + (5663253597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026459423/5000000000 : ℝ)^4225 ≤ (3092712158637/25000000000000 : ℝ)^3201 := by
    have hnat : (1026459423 : ℕ)^4225*25000000000000^3201 ≤ 3092712158637^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026459423 5000000000 3092712158637 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516946329/5000000000 : ℝ)^4225 ≤ (40415040181873/100000000000000 : ℝ)^3201 := by
    have hnat : (2516946329 : ℕ)^4225*100000000000000^3201 ≤ 40415040181873^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516946329 5000000000 40415040181873 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663253597/10000000000 : ℝ)^4225 ≤ (47214111163947/100000000000000 : ℝ)^3201 := by
    have hnat : (5663253597 : ℕ)^4225*100000000000000^3201 ≤ 47214111163947^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663253597 10000000000 47214111163947 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026459423/5000000000 : ℝ), (2516946329/5000000000 : ℝ), (5663253597/10000000000 : ℝ)] ![(3092712158637/25000000000000 : ℝ), (40415040181873/100000000000000 : ℝ), (47214111163947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026459423/5000000000 : ℝ)|^4225 ≤ (3092712158637/25000000000000 : ℝ)^3201
        have hw : |(-1026459423/5000000000 : ℝ)|=(1026459423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516946329/5000000000 : ℝ)|^4225 ≤ (40415040181873/100000000000000 : ℝ)^3201
        have hw : |(2516946329/5000000000 : ℝ)|=(2516946329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663253597/10000000000 : ℝ)|^4225 ≤ (47214111163947/100000000000000 : ℝ)^3201
        have hw : |(5663253597/10000000000 : ℝ)|=(5663253597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655774263/1250000000 : ℝ)*x 0 + (-880660421/5000000000 : ℝ)*x 1 + (5663253963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655774263/1250000000 : ℝ)^4225 ≤ (533497720881/1250000000000 : ℝ)^3201 := by
    have hnat : (655774263 : ℕ)^4225*1250000000000^3201 ≤ 533497720881^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655774263 1250000000 533497720881 1250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880660421/5000000000 : ℝ)^4225 ≤ (10106067125627/100000000000000 : ℝ)^3201 := by
    have hnat : (880660421 : ℕ)^4225*100000000000000^3201 ≤ 10106067125627^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880660421 5000000000 10106067125627 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663253963/10000000000 : ℝ)^4225 ≤ (2950882199461/6250000000000 : ℝ)^3201 := by
    have hnat : (5663253963 : ℕ)^4225*6250000000000^3201 ≤ 2950882199461^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663253963 10000000000 2950882199461 6250000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655774263/1250000000 : ℝ), (-880660421/5000000000 : ℝ), (5663253963/10000000000 : ℝ)] ![(533497720881/1250000000000 : ℝ), (10106067125627/100000000000000 : ℝ), (2950882199461/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655774263/1250000000 : ℝ)|^4225 ≤ (533497720881/1250000000000 : ℝ)^3201
        have hw : |(655774263/1250000000 : ℝ)|=(655774263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880660421/5000000000 : ℝ)|^4225 ≤ (10106067125627/100000000000000 : ℝ)^3201
        have hw : |(-880660421/5000000000 : ℝ)|=(880660421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663253963/10000000000 : ℝ)|^4225 ≤ (2950882199461/6250000000000 : ℝ)^3201
        have hw : |(5663253963/10000000000 : ℝ)|=(5663253963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655774253/1250000000 : ℝ)*x 0 + (2831626857/5000000000 : ℝ)*x 1 + (-1761321317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655774253/1250000000 : ℝ)^4225 ≤ (5334977101431/12500000000000 : ℝ)^3201 := by
    have hnat : (655774253 : ℕ)^4225*12500000000000^3201 ≤ 5334977101431^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655774253 1250000000 5334977101431 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831626857/5000000000 : ℝ)^4225 ≤ (11803528112851/25000000000000 : ℝ)^3201 := by
    have hnat : (2831626857 : ℕ)^4225*25000000000000^3201 ≤ 11803528112851^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831626857 5000000000 11803528112851 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761321317/10000000000 : ℝ)^4225 ≤ (5053035361471/50000000000000 : ℝ)^3201 := by
    have hnat : (1761321317 : ℕ)^4225*50000000000000^3201 ≤ 5053035361471^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761321317 10000000000 5053035361471 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655774253/1250000000 : ℝ), (2831626857/5000000000 : ℝ), (-1761321317/10000000000 : ℝ)] ![(5334977101431/12500000000000 : ℝ), (11803528112851/25000000000000 : ℝ), (5053035361471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655774253/1250000000 : ℝ)|^4225 ≤ (5334977101431/12500000000000 : ℝ)^3201
        have hw : |(655774253/1250000000 : ℝ)|=(655774253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831626857/5000000000 : ℝ)|^4225 ≤ (11803528112851/25000000000000 : ℝ)^3201
        have hw : |(2831626857/5000000000 : ℝ)|=(2831626857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761321317/10000000000 : ℝ)|^4225 ≤ (5053035361471/50000000000000 : ℝ)^3201
        have hw : |(-1761321317/10000000000 : ℝ)|=(1761321317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s1_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308891787/10000000000 : ℝ)*x 0 + (249802683/500000000 : ℝ)*x 1 + (185782571/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308891787/10000000000 : ℝ)^4225 ≤ (16457699629667/50000000000000 : ℝ)^3201 := by
    have hnat : (4308891787 : ℕ)^4225*50000000000000^3201 ≤ 16457699629667^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308891787 10000000000 16457699629667 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249802683/500000000 : ℝ)^4225 ≤ (5001818232581/12500000000000 : ℝ)^3201 := by
    have hnat : (249802683 : ℕ)^4225*12500000000000^3201 ≤ 5001818232581^3201*500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249802683 500000000 5001818232581 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185782571/500000000 : ℝ)^4225 ≤ (3383756858249/12500000000000 : ℝ)^3201 := by
    have hnat : (185782571 : ℕ)^4225*12500000000000^3201 ≤ 3383756858249^3201*500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185782571 500000000 3383756858249 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308891787/10000000000 : ℝ), (249802683/500000000 : ℝ), (185782571/500000000 : ℝ)] ![(16457699629667/50000000000000 : ℝ), (5001818232581/12500000000000 : ℝ), (3383756858249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308891787/10000000000 : ℝ)|^4225 ≤ (16457699629667/50000000000000 : ℝ)^3201
        have hw : |(4308891787/10000000000 : ℝ)|=(4308891787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249802683/500000000 : ℝ)|^4225 ≤ (5001818232581/12500000000000 : ℝ)^3201
        have hw : |(249802683/500000000 : ℝ)|=(249802683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185782571/500000000 : ℝ)|^4225 ≤ (3383756858249/12500000000000 : ℝ)^3201
        have hw : |(185782571/500000000 : ℝ)|=(185782571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1369/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3987/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1369/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (439/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1369/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (439/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1369/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (439/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1369/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (439/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1369/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (439/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1369/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (439/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (439/50000 : ℝ) ^ (8449/2048 : ℝ) ≤ (328027855733/100000000000000000000 : ℝ) := by
    have hpowers : (439/50000 : ℝ)^8449 ≤ (328027855733/100000000000000000000 : ℝ)^2048 := by
      have hnat : (439 : ℕ)^8449*100000000000000000000^2048 ≤ 328027855733^2048*50000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 50000 328027855733 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/50000 : ℝ)) (X := (328027855733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1369/5000 : ℝ) ^ (8449/2048 : ℝ) ≤ (238840663675287379/50000000000000000000 : ℝ) := by
    have hpowers : (1369/5000 : ℝ)^8449 ≤ (238840663675287379/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1369 : ℕ)^8449*50000000000000000000^2048 ≤ 238840663675287379^2048*5000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1369 5000 238840663675287379 50000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1369/5000 : ℝ)) (X := (238840663675287379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000328027855733/50000000000000000000 : ℝ) ≤ (10000000015902499/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50000000328027855733/50000000000000000000 : ℝ)^2048 ≤ (10000000015902499/10000000000000000 : ℝ)^8449 := by
      have hnat : (50000000328027855733 : ℕ)^2048*10000000000000000^8449 ≤ 10000000015902499^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000328027855733 50000000000000000000 10000000015902499 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000015902499/10000000000000000 : ℝ)) (X := (50000000328027855733/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100477681655378430491/100000000000000000000 : ℝ) ≤ (2502889474432287/2500000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (100477681655378430491/100000000000000000000 : ℝ)^2048 ≤ (2502889474432287/2500000000000000 : ℝ)^8449 := by
      have hnat : (100477681655378430491 : ℕ)^2048*2500000000000000^8449 ≤ 2502889474432287^8449*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100477681655378430491 100000000000000000000 2502889474432287 2500000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502889474432287/2500000000000000 : ℝ)) (X := (100477681655378430491/100000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25238840663675287379/25000000000000000000 : ℝ) ≤ (10023115779555797/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (25238840663675287379/25000000000000000000 : ℝ)^2048 ≤ (10023115779555797/10000000000000000 : ℝ)^8449 := by
      have hnat : (25238840663675287379 : ℕ)^2048*10000000000000000^8449 ≤ 10023115779555797^8449*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25238840663675287379 25000000000000000000 10023115779555797 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023115779555797/10000000000000000 : ℝ)) (X := (25238840663675287379/25000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(328027855733/100000000000000000000 : ℝ) ≤ ((132499852390480216427/132510000000000000000 : ℝ)+2*(11557881826649/2650200000000000 : ℝ)*(439/50000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (132499852390480216427/132510000000000000000 : ℝ)+2*(11557881826649/2650200000000000 : ℝ)*(439/50000 : ℝ)=(10000000015902499/10000000000000000 : ℝ) by norm_num, show 1+2*(328027855733/100000000000000000000 : ℝ)=(50000000328027855733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(238840663675287379/50000000000000000000 : ℝ)+(328027855733/100000000000000000000 : ℝ) ≤ ((132499852390480216427/132510000000000000000 : ℝ)+(11557881826649/2650200000000000 : ℝ)*((1369/5000 : ℝ)+(439/50000 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (132499852390480216427/132510000000000000000 : ℝ)+(11557881826649/2650200000000000 : ℝ)*((1369/5000 : ℝ)+(439/50000 : ℝ))=(2502889474432287/2500000000000000 : ℝ) by norm_num, show 1+(238840663675287379/50000000000000000000 : ℝ)+(328027855733/100000000000000000000 : ℝ)=(100477681655378430491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(238840663675287379/50000000000000000000 : ℝ) ≤ ((132499852390480216427/132510000000000000000 : ℝ)+2*(11557881826649/2650200000000000 : ℝ)*(1369/5000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (132499852390480216427/132510000000000000000 : ℝ)+2*(11557881826649/2650200000000000 : ℝ)*(1369/5000 : ℝ)=(10023115779555797/10000000000000000 : ℝ) by norm_num, show 1+2*(238840663675287379/50000000000000000000 : ℝ)=(25238840663675287379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132499852390480216427/132510000000000000000 : ℝ)*(X 1 0+X 2 0)+(11557881826649/2650200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (439/50000 : ℝ)) (hi := (1369/5000 : ℝ)) (c := (132499852390480216427/132510000000000000000 : ℝ)) (alpha := (11557881826649/2650200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132499852390480216427/132510000000000000000 : ℝ)*(X 0 1+X 2 1)+(11557881826649/2650200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (439/50000 : ℝ)) (hi := (1369/5000 : ℝ)) (c := (132499852390480216427/132510000000000000000 : ℝ)) (alpha := (11557881826649/2650200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132499852390480216427/132510000000000000000 : ℝ)*(X 0 2+X 1 2)+(11557881826649/2650200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (439/50000 : ℝ)) (hi := (1369/5000 : ℝ)) (c := (132499852390480216427/132510000000000000000 : ℝ)) (alpha := (11557881826649/2650200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513065067/2500000000 : ℝ)*X 0 0+(5671854317/10000000000 : ℝ)*X 0 1+(1256362869/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706421897/5000000000 : ℝ)*X 1 0+(-2399123041/10000000000 : ℝ)*X 1 1+(1256362947/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353211021/2500000000 : ℝ)*X 2 0+(2512725793/5000000000 : ℝ)*X 2 1+(-1199561461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307552143/10000000000 : ℝ)*X 0 0+(924538329/2500000000 : ℝ)*X 0 1+(2506613309/5000000000 : ℝ)*X 0 2+(4307552143/10000000000 : ℝ)*X 1 0+(924538329/2500000000 : ℝ)*X 1 1+(2506613309/5000000000 : ℝ)*X 1 2+(4307552143/10000000000 : ℝ)*X 2 0+(924538329/2500000000 : ℝ)*X 2 1+(2506613309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1026459423/5000000000 : ℝ)*X 0 0+(2516946329/5000000000 : ℝ)*X 0 1+(5663253597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655774263/1250000000 : ℝ)*X 1 0+(-880660421/5000000000 : ℝ)*X 1 1+(5663253963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655774253/1250000000 : ℝ)*X 2 0+(2831626857/5000000000 : ℝ)*X 2 1+(-1761321317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308891787/10000000000 : ℝ)*X 0 0+(249802683/500000000 : ℝ)*X 0 1+(185782571/500000000 : ℝ)*X 0 2+(4308891787/10000000000 : ℝ)*X 1 0+(249802683/500000000 : ℝ)*X 1 1+(185782571/500000000 : ℝ)*X 1 2+(4308891787/10000000000 : ℝ)*X 2 0+(249802683/500000000 : ℝ)*X 2 1+(185782571/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8297137441643030256956428781/1104250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65549901/100000000000000 : ℝ)*(base1) + (418580973/25000000000000 : ℝ)*(base19) + (1757208589/100000000000000 : ℝ)*(base23) + (173378331/100000000000000 : ℝ)*(upper3) + (119927949/50000000000000 : ℝ)*(upper5) + (1153733633633503/100000000000000 : ℝ)*(major0) + (1153733633633503/100000000000000 : ℝ)*(major1) + (1153733633633503/100000000000000 : ℝ)*(major2) + (1547032331502853/100000000000000 : ℝ)*(sp0) + (773520586233701/50000000000000 : ℝ)*(sp1) + (309408217916541/20000000000000 : ℝ)*(sp2) + (760419035585847/100000000000000 : ℝ)*(sp3) + (10580838341/100000000000000 : ℝ)*(sp4) + (126721981/2500000000000 : ℝ)*(sp7) + (190106042503747/25000000000000 : ℝ)*(f.failure) + (773521423395647/50000000000000 : ℝ)*(f.sum) + (188079764115163/132510000000000000000000000000 : ℝ)*base66 + (33949939481443167927/4417000000000000000000000000000000 : ℝ)*base67 + (7602617078896832073/4417000000000000000000000000000000 : ℝ)*base70 + (21619106756842832073/4417000000000000000000000000000000 : ℝ)*base72 + (627012480320747/132510000000000000000000000000 : ℝ)*base73 + (24836828681203832073/4417000000000000000000000000000000 : ℝ)*base76 + (13690432886186832073/4417000000000000000000000000000000 : ℝ)*base78 + (13708401069923832073/4417000000000000000000000000000000 : ℝ)*base80 + (447988763970913/132510000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3124817/1250000000000000000000 : ℝ)*base90 + (3124817/1250000000000000000000 : ℝ)*base92 + (3124817/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2710889681575706910667737131/1104250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38791653/10000000000000 : ℝ)*(base19) + (350192947/100000000000000 : ℝ)*(base23) + (8653241/100000000000000 : ℝ)*(upper2) + (19182351/25000000000000 : ℝ)*(upper3) + (49206059/100000000000000 : ℝ)*(upper5) + (1184958771414553/100000000000000 : ℝ)*(major0) + (1184958771414553/100000000000000 : ℝ)*(major1) + (1184958771414553/100000000000000 : ℝ)*(major2) + (1173203541/50000000000000 : ℝ)*(sp1) + (350589973/25000000000000 : ℝ)*(sp2) + (39722821195293/2500000000000 : ℝ)*(sp4) + (1588910113488109/100000000000000 : ℝ)*(sp5) + (1588911095258881/100000000000000 : ℝ)*(sp6) + (24406394162043/3125000000000 : ℝ)*(sp7) + (24406394162043/3125000000000 : ℝ)*(f.failure) + (39722821195293/2500000000000 : ℝ)*(f.sum) + (192177977064977/132510000000000000000000000000 : ℝ)*base65 + (22796970600132562623/4417000000000000000000000000000000 : ℝ)*base68 + (30291572064412562623/4417000000000000000000000000000000 : ℝ)*base70 + (23585570454944562623/4417000000000000000000000000000000 : ℝ)*base72 + (817998787147303/132510000000000000000000000000 : ℝ)*base74 + (38205209473243562623/4417000000000000000000000000000000 : ℝ)*base76 + (16278085872179437377/4417000000000000000000000000000000 : ℝ)*base77 + (24274770645294562623/4417000000000000000000000000000000 : ℝ)*base80 + (844168345926793/132510000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1586627/156250000000000000000 : ℝ)*base89 + (1586627/156250000000000000000 : ℝ)*base91 + (1586627/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1369/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3987/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1257_s2_0 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049780363/5000000000 : ℝ)*x 0 + (2745124659/5000000000 : ℝ)*x 1 + (1035375469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049780363/5000000000 : ℝ)^4225 ≤ (12743165023091/100000000000000 : ℝ)^3201 := by
    have hnat : (1049780363 : ℕ)^4225*100000000000000^3201 ≤ 12743165023091^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049780363 5000000000 12743165023091 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745124659/5000000000 : ℝ)^4225 ≤ (45319755758731/100000000000000 : ℝ)^3201 := by
    have hnat : (2745124659 : ℕ)^4225*100000000000000^3201 ≤ 45319755758731^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745124659 5000000000 45319755758731 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035375469/2000000000 : ℝ)^4225 ≤ (2096853960267/5000000000000 : ℝ)^3201 := by
    have hnat : (1035375469 : ℕ)^4225*5000000000000^3201 ≤ 2096853960267^3201*2000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035375469 2000000000 2096853960267 5000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049780363/5000000000 : ℝ), (2745124659/5000000000 : ℝ), (1035375469/2000000000 : ℝ)] ![(12743165023091/100000000000000 : ℝ), (45319755758731/100000000000000 : ℝ), (2096853960267/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049780363/5000000000 : ℝ)|^4225 ≤ (12743165023091/100000000000000 : ℝ)^3201
        have hw : |(-1049780363/5000000000 : ℝ)|=(1049780363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745124659/5000000000 : ℝ)|^4225 ≤ (45319755758731/100000000000000 : ℝ)^3201
        have hw : |(2745124659/5000000000 : ℝ)|=(2745124659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035375469/2000000000 : ℝ)|^4225 ≤ (2096853960267/5000000000000 : ℝ)^3201
        have hw : |(1035375469/2000000000 : ℝ)|=(1035375469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_1 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369077659/10000000000 : ℝ)*x 0 + (-226180099/1000000000 : ℝ)*x 1 + (5176877487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369077659/10000000000 : ℝ)^4225 ≤ (44004246286993/100000000000000 : ℝ)^3201 := by
    have hnat : (5369077659 : ℕ)^4225*100000000000000^3201 ≤ 44004246286993^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369077659 10000000000 44004246286993 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226180099/1000000000 : ℝ)^4225 ≤ (14058672982499/100000000000000 : ℝ)^3201 := by
    have hnat : (226180099 : ℕ)^4225*100000000000000^3201 ≤ 14058672982499^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226180099 1000000000 14058672982499 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176877487/10000000000 : ℝ)^4225 ≤ (41937080723647/100000000000000 : ℝ)^3201 := by
    have hnat : (5176877487 : ℕ)^4225*100000000000000^3201 ≤ 41937080723647^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176877487 10000000000 41937080723647 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369077659/10000000000 : ℝ), (-226180099/1000000000 : ℝ), (5176877487/10000000000 : ℝ)] ![(44004246286993/100000000000000 : ℝ), (14058672982499/100000000000000 : ℝ), (41937080723647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369077659/10000000000 : ℝ)|^4225 ≤ (44004246286993/100000000000000 : ℝ)^3201
        have hw : |(5369077659/10000000000 : ℝ)|=(5369077659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226180099/1000000000 : ℝ)|^4225 ≤ (14058672982499/100000000000000 : ℝ)^3201
        have hw : |(-226180099/1000000000 : ℝ)|=(226180099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176877487/10000000000 : ℝ)|^4225 ≤ (41937080723647/100000000000000 : ℝ)^3201
        have hw : |(5176877487/10000000000 : ℝ)|=(5176877487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_2 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83891837/156250000 : ℝ)*x 0 + (1294219383/2500000000 : ℝ)*x 1 + (-2261801051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83891837/156250000 : ℝ)^4225 ≤ (2200212265129/5000000000000 : ℝ)^3201 := by
    have hnat : (83891837 : ℕ)^4225*5000000000000^3201 ≤ 2200212265129^3201*156250000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83891837 156250000 2200212265129 5000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294219383/2500000000 : ℝ)^4225 ≤ (41937081204801/100000000000000 : ℝ)^3201 := by
    have hnat : (1294219383 : ℕ)^4225*100000000000000^3201 ≤ 41937081204801^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294219383 2500000000 41937081204801 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261801051/10000000000 : ℝ)^4225 ≤ (14058673482949/100000000000000 : ℝ)^3201 := by
    have hnat : (2261801051 : ℕ)^4225*100000000000000^3201 ≤ 14058673482949^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261801051 10000000000 14058673482949 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83891837/156250000 : ℝ), (1294219383/2500000000 : ℝ), (-2261801051/10000000000 : ℝ)] ![(2200212265129/5000000000000 : ℝ), (41937081204801/100000000000000 : ℝ), (14058673482949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83891837/156250000 : ℝ)|^4225 ≤ (2200212265129/5000000000000 : ℝ)^3201
        have hw : |(83891837/156250000 : ℝ)|=(83891837/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294219383/2500000000 : ℝ)|^4225 ≤ (41937081204801/100000000000000 : ℝ)^3201
        have hw : |(1294219383/2500000000 : ℝ)|=(1294219383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2261801051/10000000000 : ℝ)|^4225 ≤ (14058673482949/100000000000000 : ℝ)^3201
        have hw : |(-2261801051/10000000000 : ℝ)|=(2261801051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_3 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340252927/10000000000 : ℝ)*x 0 + (504097987/1250000000 : ℝ)*x 1 + (4670322299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340252927/10000000000 : ℝ)^4225 ≤ (6646394015897/20000000000000 : ℝ)^3201 := by
    have hnat : (4340252927 : ℕ)^4225*20000000000000^3201 ≤ 6646394015897^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340252927 10000000000 6646394015897 20000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504097987/1250000000 : ℝ)^4225 ≤ (15080230014471/50000000000000 : ℝ)^3201 := by
    have hnat : (504097987 : ℕ)^4225*50000000000000^3201 ≤ 15080230014471^3201*1250000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504097987 1250000000 15080230014471 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4670322299/10000000000 : ℝ)^4225 ≤ (1830378493609/5000000000000 : ℝ)^3201 := by
    have hnat : (4670322299 : ℕ)^4225*5000000000000^3201 ≤ 1830378493609^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670322299 10000000000 1830378493609 5000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340252927/10000000000 : ℝ), (504097987/1250000000 : ℝ), (4670322299/10000000000 : ℝ)] ![(6646394015897/20000000000000 : ℝ), (15080230014471/50000000000000 : ℝ), (1830378493609/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340252927/10000000000 : ℝ)|^4225 ≤ (6646394015897/20000000000000 : ℝ)^3201
        have hw : |(4340252927/10000000000 : ℝ)|=(4340252927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504097987/1250000000 : ℝ)|^4225 ≤ (15080230014471/50000000000000 : ℝ)^3201
        have hw : |(504097987/1250000000 : ℝ)|=(504097987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4670322299/10000000000 : ℝ)|^4225 ≤ (1830378493609/5000000000000 : ℝ)^3201
        have hw : |(4670322299/10000000000 : ℝ)|=(4670322299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_4 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-83985443/400000000 : ℝ)*x 0 + (5178871063/10000000000 : ℝ)*x 1 + (1372059273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83985443/400000000 : ℝ)^4225 ≤ (12743768651807/100000000000000 : ℝ)^3201 := by
    have hnat : (83985443 : ℕ)^4225*100000000000000^3201 ≤ 12743768651807^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83985443 400000000 12743768651807 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178871063/10000000000 : ℝ)^4225 ≤ (20979198979781/50000000000000 : ℝ)^3201 := by
    have hnat : (5178871063 : ℕ)^4225*50000000000000^3201 ≤ 20979198979781^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178871063 10000000000 20979198979781 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372059273/2500000000 : ℝ)^4225 ≤ (22648916686203/50000000000000 : ℝ)^3201 := by
    have hnat : (1372059273 : ℕ)^4225*50000000000000^3201 ≤ 22648916686203^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372059273 2500000000 22648916686203 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83985443/400000000 : ℝ), (5178871063/10000000000 : ℝ), (1372059273/2500000000 : ℝ)] ![(12743768651807/100000000000000 : ℝ), (20979198979781/50000000000000 : ℝ), (22648916686203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83985443/400000000 : ℝ)|^4225 ≤ (12743768651807/100000000000000 : ℝ)^3201
        have hw : |(-83985443/400000000 : ℝ)|=(83985443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178871063/10000000000 : ℝ)|^4225 ≤ (20979198979781/50000000000000 : ℝ)^3201
        have hw : |(5178871063/10000000000 : ℝ)|=(5178871063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372059273/2500000000 : ℝ)|^4225 ≤ (22648916686203/50000000000000 : ℝ)^3201
        have hw : |(1372059273/2500000000 : ℝ)|=(1372059273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_5 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288976667/10000000000 : ℝ)*x 0 + (-15603529/80000000 : ℝ)*x 1 + (5488237137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288976667/10000000000 : ℝ)^4225 ≤ (43139810556341/100000000000000 : ℝ)^3201 := by
    have hnat : (5288976667 : ℕ)^4225*100000000000000^3201 ≤ 43139810556341^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288976667 10000000000 43139810556341 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15603529/80000000 : ℝ)^4225 ≤ (11562355562259/100000000000000 : ℝ)^3201 := by
    have hnat : (15603529 : ℕ)^4225*100000000000000^3201 ≤ 11562355562259^3201*80000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15603529 80000000 11562355562259 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488237137/10000000000 : ℝ)^4225 ≤ (22648916931317/50000000000000 : ℝ)^3201 := by
    have hnat : (5488237137 : ℕ)^4225*50000000000000^3201 ≤ 22648916931317^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488237137 10000000000 22648916931317 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288976667/10000000000 : ℝ), (-15603529/80000000 : ℝ), (5488237137/10000000000 : ℝ)] ![(43139810556341/100000000000000 : ℝ), (11562355562259/100000000000000 : ℝ), (22648916931317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288976667/10000000000 : ℝ)|^4225 ≤ (43139810556341/100000000000000 : ℝ)^3201
        have hw : |(5288976667/10000000000 : ℝ)|=(5288976667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15603529/80000000 : ℝ)|^4225 ≤ (11562355562259/100000000000000 : ℝ)^3201
        have hw : |(-15603529/80000000 : ℝ)|=(15603529/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488237137/10000000000 : ℝ)|^4225 ≤ (22648916931317/50000000000000 : ℝ)^3201
        have hw : |(5488237137/10000000000 : ℝ)|=(5488237137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_6 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322244201/2500000000 : ℝ)*x 0 + (2744118621/5000000000 : ℝ)*x 1 + (-195044079/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322244201/2500000000 : ℝ)^4225 ≤ (43139812031261/100000000000000 : ℝ)^3201 := by
    have hnat : (1322244201 : ℕ)^4225*100000000000000^3201 ≤ 43139812031261^3201*2500000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322244201 2500000000 43139812031261 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744118621/5000000000 : ℝ)^4225 ≤ (45297835006499/100000000000000 : ℝ)^3201 := by
    have hnat : (2744118621 : ℕ)^4225*100000000000000^3201 ≤ 45297835006499^3201*5000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744118621 5000000000 45297835006499 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195044079/1000000000 : ℝ)^4225 ≤ (1445294117633/12500000000000 : ℝ)^3201 := by
    have hnat : (195044079 : ℕ)^4225*12500000000000^3201 ≤ 1445294117633^3201*1000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195044079 1000000000 1445294117633 12500000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322244201/2500000000 : ℝ), (2744118621/5000000000 : ℝ), (-195044079/1000000000 : ℝ)] ![(43139812031261/100000000000000 : ℝ), (45297835006499/100000000000000 : ℝ), (1445294117633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322244201/2500000000 : ℝ)|^4225 ≤ (43139812031261/100000000000000 : ℝ)^3201
        have hw : |(1322244201/2500000000 : ℝ)|=(1322244201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744118621/5000000000 : ℝ)|^4225 ≤ (45297835006499/100000000000000 : ℝ)^3201
        have hw : |(2744118621/5000000000 : ℝ)|=(2744118621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195044079/1000000000 : ℝ)|^4225 ≤ (1445294117633/12500000000000 : ℝ)^3201
        have hw : |(-195044079/1000000000 : ℝ)|=(195044079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1257_s2_7 (p : ℝ) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340405751/10000000000 : ℝ)*x 0 + (4666266619/10000000000 : ℝ)*x 1 + (161475073/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340405751/10000000000 : ℝ)^4225 ≤ (16616757268733/50000000000000 : ℝ)^3201 := by
    have hnat : (4340405751 : ℕ)^4225*50000000000000^3201 ≤ 16616757268733^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340405751 10000000000 16616757268733 50000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4666266619/10000000000 : ℝ)^4225 ≤ (36565616349909/100000000000000 : ℝ)^3201 := by
    have hnat : (4666266619 : ℕ)^4225*100000000000000^3201 ≤ 36565616349909^3201*10000000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666266619 10000000000 36565616349909 100000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161475073/400000000 : ℝ)^4225 ≤ (7550217272071/25000000000000 : ℝ)^3201 := by
    have hnat : (161475073 : ℕ)^4225*25000000000000^3201 ≤ 7550217272071^3201*400000000^4225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161475073 400000000 7550217272071 25000000000000 4225 3201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4225/1024 : ℝ)) 4225 3201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340405751/10000000000 : ℝ), (4666266619/10000000000 : ℝ), (161475073/400000000 : ℝ)] ![(16616757268733/50000000000000 : ℝ), (36565616349909/100000000000000 : ℝ), (7550217272071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340405751/10000000000 : ℝ)|^4225 ≤ (16616757268733/50000000000000 : ℝ)^3201
        have hw : |(4340405751/10000000000 : ℝ)|=(4340405751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4666266619/10000000000 : ℝ)|^4225 ≤ (36565616349909/100000000000000 : ℝ)^3201
        have hw : |(4666266619/10000000000 : ℝ)|=(4666266619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161475073/400000000 : ℝ)|^4225 ≤ (7550217272071/25000000000000 : ℝ)^3201
        have hw : |(161475073/400000000 : ℝ)|=(161475073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1257_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (239/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2023/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6269/100000 : ℝ) ^ (8449/2048 : ℝ) ≤ (1091077393548377/100000000000000000000 : ℝ) := by
    have hpowers : (6269/100000 : ℝ)^8449 ≤ (1091077393548377/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6269 : ℕ)^8449*100000000000000000000^2048 ≤ 1091077393548377^2048*100000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6269 100000 1091077393548377 100000000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6269/100000 : ℝ)) (X := (1091077393548377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3987/20000 : ℝ) ^ (8449/2048 : ℝ) ≤ (4031113510196431/3125000000000000000 : ℝ) := by
    have hpowers : (3987/20000 : ℝ)^8449 ≤ (4031113510196431/3125000000000000000 : ℝ)^2048 := by
      have hnat : (3987 : ℕ)^8449*3125000000000000000^2048 ≤ 4031113510196431^2048*20000^8449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3987 20000 4031113510196431 3125000000000000000 8449 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3987/20000 : ℝ)) (X := (4031113510196431/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001091077393548377/50000000000000000000 : ℝ) ≤ (2500013223505927/2500000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (50001091077393548377/50000000000000000000 : ℝ)^2048 ≤ (2500013223505927/2500000000000000 : ℝ)^8449 := by
      have hnat : (50001091077393548377 : ℕ)^2048*2500000000000000^8449 ≤ 2500013223505927^8449*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001091077393548377 50000000000000000000 2500013223505927 2500000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500013223505927/2500000000000000 : ℝ)) (X := (50001091077393548377/50000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100130086709719834169/100000000000000000000 : ℝ) ≤ (10003151691306907/10000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (100130086709719834169/100000000000000000000 : ℝ)^2048 ≤ (10003151691306907/10000000000000000 : ℝ)^8449 := by
      have hnat : (100130086709719834169 : ℕ)^2048*10000000000000000^8449 ≤ 10003151691306907^8449*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100130086709719834169 100000000000000000000 10003151691306907 10000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003151691306907/10000000000000000 : ℝ)) (X := (100130086709719834169/100000000000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1566531113510196431/1562500000000000000 : ℝ) ≤ (5003125244295053/5000000000000000 : ℝ) ^ (8449/2048 : ℝ) := by
    have hpowers : (1566531113510196431/1562500000000000000 : ℝ)^2048 ≤ (5003125244295053/5000000000000000 : ℝ)^8449 := by
      have hnat : (1566531113510196431 : ℕ)^2048*5000000000000000^8449 ≤ 5003125244295053^8449*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1566531113510196431 1562500000000000000 5003125244295053 5000000000000000 2048 8449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003125244295053/5000000000000000 : ℝ)) (X := (1566531113510196431/1562500000000000000 : ℝ)) (by norm_num) 8449 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1091077393548377/100000000000000000000 : ℝ) ≤ ((68310935064695622233/68330000000000000000 : ℝ)+2*(3098797283199/1366600000000000 : ℝ)*(6269/100000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (68310935064695622233/68330000000000000000 : ℝ)+2*(3098797283199/1366600000000000 : ℝ)*(6269/100000 : ℝ)=(2500013223505927/2500000000000000 : ℝ) by norm_num, show 1+2*(1091077393548377/100000000000000000000 : ℝ)=(50001091077393548377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4031113510196431/3125000000000000000 : ℝ)+(1091077393548377/100000000000000000000 : ℝ) ≤ ((68310935064695622233/68330000000000000000 : ℝ)+(3098797283199/1366600000000000 : ℝ)*((3987/20000 : ℝ)+(6269/100000 : ℝ)))^(8449/2048 : ℝ) := by
    rw [show (68310935064695622233/68330000000000000000 : ℝ)+(3098797283199/1366600000000000 : ℝ)*((3987/20000 : ℝ)+(6269/100000 : ℝ))=(10003151691306907/10000000000000000 : ℝ) by norm_num, show 1+(4031113510196431/3125000000000000000 : ℝ)+(1091077393548377/100000000000000000000 : ℝ)=(100130086709719834169/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4031113510196431/3125000000000000000 : ℝ) ≤ ((68310935064695622233/68330000000000000000 : ℝ)+2*(3098797283199/1366600000000000 : ℝ)*(3987/20000 : ℝ))^(8449/2048 : ℝ) := by
    rw [show (68310935064695622233/68330000000000000000 : ℝ)+2*(3098797283199/1366600000000000 : ℝ)*(3987/20000 : ℝ)=(5003125244295053/5000000000000000 : ℝ) by norm_num, show 1+2*(4031113510196431/3125000000000000000 : ℝ)=(1566531113510196431/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68310935064695622233/68330000000000000000 : ℝ)*(X 1 0+X 2 0)+(3098797283199/1366600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (6269/100000 : ℝ)) (hi := (3987/20000 : ℝ)) (c := (68310935064695622233/68330000000000000000 : ℝ)) (alpha := (3098797283199/1366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68310935064695622233/68330000000000000000 : ℝ)*(X 0 1+X 2 1)+(3098797283199/1366600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (6269/100000 : ℝ)) (hi := (3987/20000 : ℝ)) (c := (68310935064695622233/68330000000000000000 : ℝ)) (alpha := (3098797283199/1366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68310935064695622233/68330000000000000000 : ℝ)*(X 0 2+X 1 2)+(3098797283199/1366600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8449/2048 : ℝ)) (lo := (6269/100000 : ℝ)) (hi := (3987/20000 : ℝ)) (c := (68310935064695622233/68330000000000000000 : ℝ)) (alpha := (3098797283199/1366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049780363/5000000000 : ℝ)*X 0 0+(2745124659/5000000000 : ℝ)*X 0 1+(1035375469/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369077659/10000000000 : ℝ)*X 1 0+(-226180099/1000000000 : ℝ)*X 1 1+(5176877487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83891837/156250000 : ℝ)*X 2 0+(1294219383/2500000000 : ℝ)*X 2 1+(-2261801051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340252927/10000000000 : ℝ)*X 0 0+(504097987/1250000000 : ℝ)*X 0 1+(4670322299/10000000000 : ℝ)*X 0 2+(4340252927/10000000000 : ℝ)*X 1 0+(504097987/1250000000 : ℝ)*X 1 1+(4670322299/10000000000 : ℝ)*X 1 2+(4340252927/10000000000 : ℝ)*X 2 0+(504097987/1250000000 : ℝ)*X 2 1+(4670322299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83985443/400000000 : ℝ)*X 0 0+(5178871063/10000000000 : ℝ)*X 0 1+(1372059273/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288976667/10000000000 : ℝ)*X 1 0+(-15603529/80000000 : ℝ)*X 1 1+(5488237137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322244201/2500000000 : ℝ)*X 2 0+(2744118621/5000000000 : ℝ)*X 2 1+(-195044079/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340405751/10000000000 : ℝ)*X 0 0+(4666266619/10000000000 : ℝ)*X 0 1+(161475073/400000000 : ℝ)*X 0 2+(4340405751/10000000000 : ℝ)*X 1 0+(4666266619/10000000000 : ℝ)*X 1 1+(161475073/400000000 : ℝ)*X 1 2+(4340405751/10000000000 : ℝ)*X 2 0+(4666266619/10000000000 : ℝ)*X 2 1+(161475073/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1257_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14085600641916165125049/2733200000000000000000000000 : ℝ) := by norm_num
    linear_combination (89031399/10000000000000 : ℝ)*(base19) + (6323493/800000000000 : ℝ)*(base23) + (24585763/100000000000000 : ℝ)*(lower2) + (150526893/100000000000000 : ℝ)*(upper3) + (9231/16000000000 : ℝ)*(upper5) + (475966164230647/20000000000000 : ℝ)*(major0) + (475966164230647/20000000000000 : ℝ)*(major1) + (475966164230647/20000000000000 : ℝ)*(major2) + (24930531284879/781250000000 : ℝ)*(sp0) + (398889690803197/12500000000000 : ℝ)*(sp1) + (1595558813151471/50000000000000 : ℝ)*(sp2) + (1568537574927793/100000000000000 : ℝ)*(sp3) + (2082455011/20000000000000 : ℝ)*(sp4) + (5478855107/100000000000000 : ℝ)*(sp7) + (15685430537829/1000000000000 : ℝ)*(f.failure) + (1595559208369783/50000000000000 : ℝ)*(f.sum) + (50056482946507/13666000000000000000000000000 : ℝ)*base65 + (1598321493383624751/1366600000000000000000000000000000 : ℝ)*base67 + (6972913131880375249/1366600000000000000000000000000000 : ℝ)*base70 + (7208766586117624751/1366600000000000000000000000000000 : ℝ)*base71 + (1915573204233/13666000000000000000000000000 : ℝ)*base74 + (9690789189159575249/1366600000000000000000000000000000 : ℝ)*base76 + (6611837794282424751/1366600000000000000000000000000000 : ℝ)*base77 + (15300866695192175249/1366600000000000000000000000000000 : ℝ)*base80 + (6522174340687/13666000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (81319/50000000000000000000 : ℝ)*base90 + (81319/50000000000000000000 : ℝ)*base92 + (81319/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (863190498157223449088689359/213531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301125263/25000000000000 : ℝ)*(base19) + (74778521/5000000000000 : ℝ)*(base23) + (7244157/12500000000000 : ℝ)*(upper2) + (89805821/50000000000000 : ℝ)*(upper3) + (75661257/100000000000000 : ℝ)*(upper5) + (301328530092841/12500000000000 : ℝ)*(major0) + (301328530092841/12500000000000 : ℝ)*(major1) + (301328530092841/12500000000000 : ℝ)*(major2) + (12152394713/100000000000000 : ℝ)*(sp1) + (4651968093/25000000000000 : ℝ)*(sp2) + (101012961194543/3125000000000 : ℝ)*(sp4) + (323240140132961/10000000000000 : ℝ)*(sp5) + (404049331847823/12500000000000 : ℝ)*(sp6) + (158884158851157/10000000000000 : ℝ)*(sp7) + (158884158851157/10000000000000 : ℝ)*(f.failure) + (101012961194543/3125000000000 : ℝ)*(f.sum) + (2135021177443/17082500000000000000000000000 : ℝ)*base65 + (1850397105765066047/854125000000000000000000000000000 : ℝ)*base68 + (8841184164376566047/854125000000000000000000000000000 : ℝ)*base70 + (2807264194732191047/854125000000000000000000000000000 : ℝ)*base72 + (41426396748143/17082500000000000000000000000 : ℝ)*base73 + (564093382361308953/854125000000000000000000000000000 : ℝ)*base75 + (9782993688124066047/854125000000000000000000000000000 : ℝ)*base78 + (2579345426909066047/854125000000000000000000000000000 : ℝ)*base80 + (55444979475017/17082500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4045673/500000000000000000000 : ℝ)*base89 + (4045673/500000000000000000000 : ℝ)*base91 + (4045673/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1257_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1257_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1257_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1257_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1257_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1257_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8449/2048 : ℝ) ≤ p) (hpb : p ≤ (4225/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75861189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (239/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1257_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
