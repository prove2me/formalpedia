-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:30.658554+00:00
-- url     : https://prove2.me/submissions/81262964-c802-49d9-bbf7-e05ee00dfbd7

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
theorem support_rectangle_w1287_s3_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32656801/156250000 : ℝ)*x 0 + (679352913/1250000000 : ℝ)*x 1 + (5225063541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32656801/156250000 : ℝ)^4247 ≤ (12710284110761/100000000000000 : ℝ)^3223 := by
    have hnat : (32656801 : ℕ)^4247*100000000000000^3223 ≤ 12710284110761^3223*156250000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32656801 156250000 12710284110761 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679352913/1250000000 : ℝ)^4247 ≤ (8955286591477/20000000000000 : ℝ)^3223 := by
    have hnat : (679352913 : ℕ)^4247*20000000000000^3223 ≤ 8955286591477^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679352913 1250000000 8955286591477 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225063541/10000000000 : ℝ)^4247 ≤ (10628320729169/25000000000000 : ℝ)^3223 := by
    have hnat : (5225063541 : ℕ)^4247*25000000000000^3223 ≤ 10628320729169^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225063541 10000000000 10628320729169 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32656801/156250000 : ℝ), (679352913/1250000000 : ℝ), (5225063541/10000000000 : ℝ)] ![(12710284110761/100000000000000 : ℝ), (8955286591477/20000000000000 : ℝ), (10628320729169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32656801/156250000 : ℝ)|^4247 ≤ (12710284110761/100000000000000 : ℝ)^3223
        have hw : |(-32656801/156250000 : ℝ)|=(32656801/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679352913/1250000000 : ℝ)|^4247 ≤ (8955286591477/20000000000000 : ℝ)^3223
        have hw : |(679352913/1250000000 : ℝ)|=(679352913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225063541/10000000000 : ℝ)|^4247 ≤ (10628320729169/25000000000000 : ℝ)^3223
        have hw : |(5225063541/10000000000 : ℝ)|=(5225063541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334671427/625000000 : ℝ)*x 0 + (-2197404009/10000000000 : ℝ)*x 1 + (522506361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334671427/625000000 : ℝ)^4247 ≤ (10977272202931/25000000000000 : ℝ)^3223 := by
    have hnat : (334671427 : ℕ)^4247*25000000000000^3223 ≤ 10977272202931^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334671427 625000000 10977272202931 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197404009/10000000000 : ℝ)^4247 ≤ (13577627518933/100000000000000 : ℝ)^3223 := by
    have hnat : (2197404009 : ℕ)^4247*100000000000000^3223 ≤ 13577627518933^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197404009 10000000000 13577627518933 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522506361/1000000000 : ℝ)^4247 ≤ (21256641828229/50000000000000 : ℝ)^3223 := by
    have hnat : (522506361 : ℕ)^4247*50000000000000^3223 ≤ 21256641828229^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522506361 1000000000 21256641828229 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334671427/625000000 : ℝ), (-2197404009/10000000000 : ℝ), (522506361/1000000000 : ℝ)] ![(10977272202931/25000000000000 : ℝ), (13577627518933/100000000000000 : ℝ), (21256641828229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334671427/625000000 : ℝ)|^4247 ≤ (10977272202931/25000000000000 : ℝ)^3223
        have hw : |(334671427/625000000 : ℝ)|=(334671427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197404009/10000000000 : ℝ)|^4247 ≤ (13577627518933/100000000000000 : ℝ)^3223
        have hw : |(-2197404009/10000000000 : ℝ)|=(2197404009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522506361/1000000000 : ℝ)|^4247 ≤ (21256641828229/50000000000000 : ℝ)^3223
        have hw : |(522506361/1000000000 : ℝ)|=(522506361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354742907/10000000000 : ℝ)*x 0 + (2612531623/5000000000 : ℝ)*x 1 + (-549351097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354742907/10000000000 : ℝ)^4247 ≤ (43909089622123/100000000000000 : ℝ)^3223 := by
    have hnat : (5354742907 : ℕ)^4247*100000000000000^3223 ≤ 43909089622123^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354742907 10000000000 43909089622123 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612531623/5000000000 : ℝ)^4247 ≤ (42513279753837/100000000000000 : ℝ)^3223 := by
    have hnat : (2612531623 : ℕ)^4247*100000000000000^3223 ≤ 42513279753837^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612531623 5000000000 42513279753837 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549351097/2500000000 : ℝ)^4247 ≤ (2715526120957/20000000000000 : ℝ)^3223 := by
    have hnat : (549351097 : ℕ)^4247*20000000000000^3223 ≤ 2715526120957^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549351097 2500000000 2715526120957 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354742907/10000000000 : ℝ), (2612531623/5000000000 : ℝ), (-549351097/2500000000 : ℝ)] ![(43909089622123/100000000000000 : ℝ), (42513279753837/100000000000000 : ℝ), (2715526120957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354742907/10000000000 : ℝ)|^4247 ≤ (43909089622123/100000000000000 : ℝ)^3223
        have hw : |(5354742907/10000000000 : ℝ)|=(5354742907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612531623/5000000000 : ℝ)|^4247 ≤ (42513279753837/100000000000000 : ℝ)^3223
        have hw : |(2612531623/5000000000 : ℝ)|=(2612531623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-549351097/2500000000 : ℝ)|^4247 ≤ (2715526120957/20000000000000 : ℝ)^3223
        have hw : |(-549351097/2500000000 : ℝ)|=(549351097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169875409/5000000000 : ℝ)*x 0 + (4129714337/10000000000 : ℝ)*x 1 + (911999481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169875409/5000000000 : ℝ)^4247 ≤ (16643758768653/50000000000000 : ℝ)^3223 := by
    have hnat : (2169875409 : ℕ)^4247*50000000000000^3223 ≤ 16643758768653^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169875409 5000000000 16643758768653 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129714337/10000000000 : ℝ)^4247 ≤ (6236220904273/20000000000000 : ℝ)^3223 := by
    have hnat : (4129714337 : ℕ)^4247*20000000000000^3223 ≤ 6236220904273^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129714337 10000000000 6236220904273 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911999481/2000000000 : ℝ)^4247 ≤ (1421255117081/4000000000000 : ℝ)^3223 := by
    have hnat : (911999481 : ℕ)^4247*4000000000000^3223 ≤ 1421255117081^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911999481 2000000000 1421255117081 4000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169875409/5000000000 : ℝ), (4129714337/10000000000 : ℝ), (911999481/2000000000 : ℝ)] ![(16643758768653/50000000000000 : ℝ), (6236220904273/20000000000000 : ℝ), (1421255117081/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169875409/5000000000 : ℝ)|^4247 ≤ (16643758768653/50000000000000 : ℝ)^3223
        have hw : |(2169875409/5000000000 : ℝ)|=(2169875409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129714337/10000000000 : ℝ)|^4247 ≤ (6236220904273/20000000000000 : ℝ)^3223
        have hw : |(4129714337/10000000000 : ℝ)|=(4129714337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911999481/2000000000 : ℝ)|^4247 ≤ (1421255117081/4000000000000 : ℝ)^3223
        have hw : |(911999481/2000000000 : ℝ)|=(911999481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090057931/10000000000 : ℝ)*x 0 + (2612985153/5000000000 : ℝ)*x 1 + (1358477757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090057931/10000000000 : ℝ)^4247 ≤ (12710465753647/100000000000000 : ℝ)^3223 := by
    have hnat : (2090057931 : ℕ)^4247*100000000000000^3223 ≤ 12710465753647^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090057931 10000000000 12710465753647 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612985153/5000000000 : ℝ)^4247 ≤ (5315375631727/12500000000000 : ℝ)^3223 := by
    have hnat : (2612985153 : ℕ)^4247*12500000000000^3223 ≤ 5315375631727^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612985153 5000000000 5315375631727 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358477757/2500000000 : ℝ)^4247 ≤ (22383264592071/50000000000000 : ℝ)^3223 := by
    have hnat : (1358477757 : ℕ)^4247*50000000000000^3223 ≤ 22383264592071^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358477757 2500000000 22383264592071 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090057931/10000000000 : ℝ), (2612985153/5000000000 : ℝ), (1358477757/2500000000 : ℝ)] ![(12710465753647/100000000000000 : ℝ), (5315375631727/12500000000000 : ℝ), (22383264592071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090057931/10000000000 : ℝ)|^4247 ≤ (12710465753647/100000000000000 : ℝ)^3223
        have hw : |(-2090057931/10000000000 : ℝ)|=(2090057931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612985153/5000000000 : ℝ)|^4247 ≤ (5315375631727/12500000000000 : ℝ)^3223
        have hw : |(2612985153/5000000000 : ℝ)|=(2612985153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358477757/2500000000 : ℝ)|^4247 ≤ (22383264592071/50000000000000 : ℝ)^3223
        have hw : |(1358477757/2500000000 : ℝ)|=(1358477757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301067529/10000000000 : ℝ)*x 0 + (-1988557049/10000000000 : ℝ)*x 1 + (2716955811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301067529/10000000000 : ℝ)^4247 ≤ (21665017736541/50000000000000 : ℝ)^3223 := by
    have hnat : (5301067529 : ℕ)^4247*50000000000000^3223 ≤ 21665017736541^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301067529 10000000000 21665017736541 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988557049/10000000000 : ℝ)^4247 ≤ (11903428881487/100000000000000 : ℝ)^3223 := by
    have hnat : (1988557049 : ℕ)^4247*100000000000000^3223 ≤ 11903428881487^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988557049 10000000000 11903428881487 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716955811/5000000000 : ℝ)^4247 ≤ (44766535632503/100000000000000 : ℝ)^3223 := by
    have hnat : (2716955811 : ℕ)^4247*100000000000000^3223 ≤ 44766535632503^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716955811 5000000000 44766535632503 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301067529/10000000000 : ℝ), (-1988557049/10000000000 : ℝ), (2716955811/5000000000 : ℝ)] ![(21665017736541/50000000000000 : ℝ), (11903428881487/100000000000000 : ℝ), (44766535632503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301067529/10000000000 : ℝ)|^4247 ≤ (21665017736541/50000000000000 : ℝ)^3223
        have hw : |(5301067529/10000000000 : ℝ)|=(5301067529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988557049/10000000000 : ℝ)|^4247 ≤ (11903428881487/100000000000000 : ℝ)^3223
        have hw : |(-1988557049/10000000000 : ℝ)|=(1988557049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716955811/5000000000 : ℝ)|^4247 ≤ (44766535632503/100000000000000 : ℝ)^3223
        have hw : |(2716955811/5000000000 : ℝ)|=(2716955811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66263363/125000000 : ℝ)*x 0 + (5433910853/10000000000 : ℝ)*x 1 + (-1988556043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66263363/125000000 : ℝ)^4247 ≤ (43330051747751/100000000000000 : ℝ)^3223 := by
    have hnat : (66263363 : ℕ)^4247*100000000000000^3223 ≤ 43330051747751^3223*125000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66263363 125000000 43330051747751 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433910853/10000000000 : ℝ)^4247 ≤ (44766527284373/100000000000000 : ℝ)^3223 := by
    have hnat : (5433910853 : ℕ)^4247*100000000000000^3223 ≤ 44766527284373^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433910853 10000000000 44766527284373 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988556043/10000000000 : ℝ)^4247 ≤ (11903420946359/100000000000000 : ℝ)^3223 := by
    have hnat : (1988556043 : ℕ)^4247*100000000000000^3223 ≤ 11903420946359^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988556043 10000000000 11903420946359 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66263363/125000000 : ℝ), (5433910853/10000000000 : ℝ), (-1988556043/10000000000 : ℝ)] ![(43330051747751/100000000000000 : ℝ), (44766527284373/100000000000000 : ℝ), (11903420946359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66263363/125000000 : ℝ)|^4247 ≤ (43330051747751/100000000000000 : ℝ)^3223
        have hw : |(66263363/125000000 : ℝ)|=(66263363/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433910853/10000000000 : ℝ)|^4247 ≤ (44766527284373/100000000000000 : ℝ)^3223
        have hw : |(5433910853/10000000000 : ℝ)|=(5433910853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988556043/10000000000 : ℝ)|^4247 ≤ (11903420946359/100000000000000 : ℝ)^3223
        have hw : |(-1988556043/10000000000 : ℝ)|=(1988556043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s3_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084949499/2500000000 : ℝ)*x 0 + (4558137583/10000000000 : ℝ)*x 1 + (413158547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084949499/2500000000 : ℝ)^4247 ≤ (33287994384077/100000000000000 : ℝ)^3223 := by
    have hnat : (1084949499 : ℕ)^4247*100000000000000^3223 ≤ 33287994384077^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084949499 2500000000 33287994384077 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4558137583/10000000000 : ℝ)^4247 ≤ (7102456647083/20000000000000 : ℝ)^3223 := by
    have hnat : (4558137583 : ℕ)^4247*20000000000000^3223 ≤ 7102456647083^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558137583 10000000000 7102456647083 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413158547/1000000000 : ℝ)^4247 ≤ (15599861181937/50000000000000 : ℝ)^3223 := by
    have hnat : (413158547 : ℕ)^4247*50000000000000^3223 ≤ 15599861181937^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413158547 1000000000 15599861181937 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084949499/2500000000 : ℝ), (4558137583/10000000000 : ℝ), (413158547/1000000000 : ℝ)] ![(33287994384077/100000000000000 : ℝ), (7102456647083/20000000000000 : ℝ), (15599861181937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084949499/2500000000 : ℝ)|^4247 ≤ (33287994384077/100000000000000 : ℝ)^3223
        have hw : |(1084949499/2500000000 : ℝ)|=(1084949499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4558137583/10000000000 : ℝ)|^4247 ≤ (7102456647083/20000000000000 : ℝ)^3223
        have hw : |(4558137583/10000000000 : ℝ)|=(4558137583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413158547/1000000000 : ℝ)|^4247 ≤ (15599861181937/50000000000000 : ℝ)^3223
        have hw : |(413158547/1000000000 : ℝ)|=(413158547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2659/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2367/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2367/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2367/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2367/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2367/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2367/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2367/25000 : ℝ) ^ (2123/512 : ℝ) ≤ (227578283702761/4000000000000000000 : ℝ) := by
    have hpowers : (2367/25000 : ℝ)^2123 ≤ (227578283702761/4000000000000000000 : ℝ)^512 := by
      have hnat : (2367 : ℕ)^2123*4000000000000000000^512 ≤ 227578283702761^512*25000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2367 25000 227578283702761 4000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2367/25000 : ℝ)) (X := (227578283702761/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (817/5000 : ℝ) ^ (2123/512 : ℝ) ≤ (10934323609920079/20000000000000000000 : ℝ) := by
    have hpowers : (817/5000 : ℝ)^2123 ≤ (10934323609920079/20000000000000000000 : ℝ)^512 := by
      have hnat : (817 : ℕ)^2123*20000000000000000000^512 ≤ 10934323609920079^512*5000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        817 5000 10934323609920079 20000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (817/5000 : ℝ)) (X := (10934323609920079/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000227578283702761/2000000000000000000 : ℝ) ≤ (2500068602832679/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (2000227578283702761/2000000000000000000 : ℝ)^512 ≤ (2500068602832679/2500000000000000 : ℝ)^2123 := by
      have hnat : (2000227578283702761 : ℕ)^512*2500000000000000^2123 ≤ 2500068602832679^2123*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000227578283702761 2000000000000000000 2500068602832679 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500068602832679/2500000000000000 : ℝ)) (X := (2000227578283702761/2000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5003018053757108471/5000000000000000000 : ℝ) ≤ (2500363845915657/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (5003018053757108471/5000000000000000000 : ℝ)^512 ≤ (2500363845915657/2500000000000000 : ℝ)^2123 := by
      have hnat : (5003018053757108471 : ℕ)^512*2500000000000000^2123 ≤ 2500363845915657^2123*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003018053757108471 5000000000000000000 2500363845915657 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500363845915657/2500000000000000 : ℝ)) (X := (5003018053757108471/5000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010934323609920079/10000000000000000000 : ℝ) ≤ (500131817799727/500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (10010934323609920079/10000000000000000000 : ℝ)^512 ≤ (500131817799727/500000000000000 : ℝ)^2123 := by
      have hnat : (10010934323609920079 : ℕ)^512*500000000000000^2123 ≤ 500131817799727^2123*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010934323609920079 10000000000000000000 500131817799727 500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500131817799727/500000000000000 : ℝ)) (X := (10010934323609920079/10000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(227578283702761/4000000000000000000 : ℝ) ≤ ((429372017891172467/429500000000000000 : ℝ)+2*(147621541489/85900000000000 : ℝ)*(2367/25000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (429372017891172467/429500000000000000 : ℝ)+2*(147621541489/85900000000000 : ℝ)*(2367/25000 : ℝ)=(2500068602832679/2500000000000000 : ℝ) by norm_num, show 1+2*(227578283702761/4000000000000000000 : ℝ)=(2000227578283702761/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10934323609920079/20000000000000000000 : ℝ)+(227578283702761/4000000000000000000 : ℝ) ≤ ((429372017891172467/429500000000000000 : ℝ)+(147621541489/85900000000000 : ℝ)*((817/5000 : ℝ)+(2367/25000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (429372017891172467/429500000000000000 : ℝ)+(147621541489/85900000000000 : ℝ)*((817/5000 : ℝ)+(2367/25000 : ℝ))=(2500363845915657/2500000000000000 : ℝ) by norm_num, show 1+(10934323609920079/20000000000000000000 : ℝ)+(227578283702761/4000000000000000000 : ℝ)=(5003018053757108471/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10934323609920079/20000000000000000000 : ℝ) ≤ ((429372017891172467/429500000000000000 : ℝ)+2*(147621541489/85900000000000 : ℝ)*(817/5000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (429372017891172467/429500000000000000 : ℝ)+2*(147621541489/85900000000000 : ℝ)*(817/5000 : ℝ)=(500131817799727/500000000000000 : ℝ) by norm_num, show 1+2*(10934323609920079/20000000000000000000 : ℝ)=(10010934323609920079/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (429372017891172467/429500000000000000 : ℝ)*(X 1 0+X 2 0)+(147621541489/85900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2367/25000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (429372017891172467/429500000000000000 : ℝ)) (alpha := (147621541489/85900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (429372017891172467/429500000000000000 : ℝ)*(X 0 1+X 2 1)+(147621541489/85900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2367/25000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (429372017891172467/429500000000000000 : ℝ)) (alpha := (147621541489/85900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (429372017891172467/429500000000000000 : ℝ)*(X 0 2+X 1 2)+(147621541489/85900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2367/25000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (429372017891172467/429500000000000000 : ℝ)) (alpha := (147621541489/85900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32656801/156250000 : ℝ)*X 0 0+(679352913/1250000000 : ℝ)*X 0 1+(5225063541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334671427/625000000 : ℝ)*X 1 0+(-2197404009/10000000000 : ℝ)*X 1 1+(522506361/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354742907/10000000000 : ℝ)*X 2 0+(2612531623/5000000000 : ℝ)*X 2 1+(-549351097/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169875409/5000000000 : ℝ)*X 0 0+(4129714337/10000000000 : ℝ)*X 0 1+(911999481/2000000000 : ℝ)*X 0 2+(2169875409/5000000000 : ℝ)*X 1 0+(4129714337/10000000000 : ℝ)*X 1 1+(911999481/2000000000 : ℝ)*X 1 2+(2169875409/5000000000 : ℝ)*X 2 0+(4129714337/10000000000 : ℝ)*X 2 1+(911999481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2090057931/10000000000 : ℝ)*X 0 0+(2612985153/5000000000 : ℝ)*X 0 1+(1358477757/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301067529/10000000000 : ℝ)*X 1 0+(-1988557049/10000000000 : ℝ)*X 1 1+(2716955811/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66263363/125000000 : ℝ)*X 2 0+(5433910853/10000000000 : ℝ)*X 2 1+(-1988556043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1084949499/2500000000 : ℝ)*X 0 0+(4558137583/10000000000 : ℝ)*X 0 1+(413158547/1000000000 : ℝ)*X 0 2+(1084949499/2500000000 : ℝ)*X 1 0+(4558137583/10000000000 : ℝ)*X 1 1+(413158547/1000000000 : ℝ)*X 1 2+(1084949499/2500000000 : ℝ)*X 2 0+(4558137583/10000000000 : ℝ)*X 2 1+(413158547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23985620113751072771369781/10737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183667829/50000000000000 : ℝ)*(base19) + (559724857/100000000000000 : ℝ)*(base23) + (165755409/100000000000000 : ℝ)*(upper3) + (39340953/50000000000000 : ℝ)*(lower4) + (3545713994162881/100000000000000 : ℝ)*(major0) + (3545713994162881/100000000000000 : ℝ)*(major1) + (3545713994162881/100000000000000 : ℝ)*(major2) + (4767366697959923/100000000000000 : ℝ)*(sp0) + (2383684183755649/50000000000000 : ℝ)*(sp1) + (2383683023943087/50000000000000 : ℝ)*(sp2) + (1162027236950723/50000000000000 : ℝ)*(sp3) + (1018443517/50000000000000 : ℝ)*(sp4) + (1063617963/50000000000000 : ℝ)*(sp6) + (4705116751/100000000000000 : ℝ)*(sp7) + (581014794754549/25000000000000 : ℝ)*(f.failure) + (1191842183711739/25000000000000 : ℝ)*(f.sum) + (9307079640899/4295000000000000000000000000 : ℝ)*base65 + (252667447916807573/42950000000000000000000000000000 : ℝ)*base68 + (227799044180607573/42950000000000000000000000000000 : ℝ)*base70 + (362797993417642427/42950000000000000000000000000000 : ℝ)*base71 + (9208503862913/2147500000000000000000000000 : ℝ)*base74 + (651044986661357573/42950000000000000000000000000000 : ℝ)*base76 + (325247388082257573/42950000000000000000000000000000 : ℝ)*base78 + (416006628030507573/42950000000000000000000000000000 : ℝ)*base80 + (6544050674841/4295000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3812341/625000000000000000000 : ℝ)*base90 + (3812341/625000000000000000000 : ℝ)*base92 + (3812341/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103923424265254919052892623/10737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327821219/100000000000000 : ℝ)*(base19) + (2676982803/100000000000000 : ℝ)*(base23) + (316680291/100000000000000 : ℝ)*(upper3) + (290718331/100000000000000 : ℝ)*(lower4) + (28047507/20000000000000 : ℝ)*(upper5) + (1788362150759923/50000000000000 : ℝ)*(major0) + (1788362150759923/50000000000000 : ℝ)*(major1) + (1788362150759923/50000000000000 : ℝ)*(major2) + (5681841469/100000000000000 : ℝ)*(sp1) + (48149408857/100000000000000 : ℝ)*(sp2) + (961812642458861/20000000000000 : ℝ)*(sp4) + (4809057202631617/100000000000000 : ℝ)*(sp5) + (961802477180529/20000000000000 : ℝ)*(sp6) + (586096267031767/25000000000000 : ℝ)*(sp7) + (586096267031767/25000000000000 : ℝ)*(f.failure) + (961812642458861/20000000000000 : ℝ)*(f.sum) + (20962415169341/4295000000000000000000000000 : ℝ)*base66 + (97807899389725041/21475000000000000000000000000000 : ℝ)*base67 + (38452984081124959/21475000000000000000000000000000 : ℝ)*base70 + (105260051833899959/21475000000000000000000000000000 : ℝ)*base72 + (1262717254911/1073750000000000000000000000 : ℝ)*base73 + (58654523539024959/21475000000000000000000000000000 : ℝ)*base76 + (104942112296550041/21475000000000000000000000000000 : ℝ)*base77 + (119982287948849959/21475000000000000000000000000000 : ℝ)*base80 + (569029039461/4295000000000000000000000000 : ℝ)*base82 + (2932103/625000000000000000000 : ℝ)*base90 + (2932103/625000000000000000000 : ℝ)*base92 + (2932103/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2659/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s4_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092007001/10000000000 : ℝ)*x 0 + (2709659097/5000000000 : ℝ)*x 1 + (5239276557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092007001/10000000000 : ℝ)^4247 ≤ (12726087042117/100000000000000 : ℝ)^3223 := by
    have hnat : (2092007001 : ℕ)^4247*100000000000000^3223 ≤ 12726087042117^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092007001 10000000000 12726087042117 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709659097/5000000000 : ℝ)^4247 ≤ (22304089774151/50000000000000 : ℝ)^3223 := by
    have hnat : (2709659097 : ℕ)^4247*50000000000000^3223 ≤ 22304089774151^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709659097 5000000000 22304089774151 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239276557/10000000000 : ℝ)^4247 ≤ (8533146678063/20000000000000 : ℝ)^3223 := by
    have hnat : (5239276557 : ℕ)^4247*20000000000000^3223 ≤ 8533146678063^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239276557 10000000000 8533146678063 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092007001/10000000000 : ℝ), (2709659097/5000000000 : ℝ), (5239276557/10000000000 : ℝ)] ![(12726087042117/100000000000000 : ℝ), (22304089774151/50000000000000 : ℝ), (8533146678063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092007001/10000000000 : ℝ)|^4247 ≤ (12726087042117/100000000000000 : ℝ)^3223
        have hw : |(-2092007001/10000000000 : ℝ)|=(2092007001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709659097/5000000000 : ℝ)|^4247 ≤ (22304089774151/50000000000000 : ℝ)^3223
        have hw : |(2709659097/5000000000 : ℝ)|=(2709659097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239276557/10000000000 : ℝ)|^4247 ≤ (8533146678063/20000000000000 : ℝ)^3223
        have hw : |(5239276557/10000000000 : ℝ)|=(5239276557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214033121/400000000 : ℝ)*x 0 + (-272982737/1250000000 : ℝ)*x 1 + (209571059/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214033121/400000000 : ℝ)^4247 ≤ (10966698242599/25000000000000 : ℝ)^3223 := by
    have hnat : (214033121 : ℕ)^4247*25000000000000^3223 ≤ 10966698242599^3223*400000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214033121 400000000 10966698242599 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272982737/1250000000 : ℝ)^4247 ≤ (3366868626371/25000000000000 : ℝ)^3223 := by
    have hnat : (272982737 : ℕ)^4247*25000000000000^3223 ≤ 3366868626371^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272982737 1250000000 3366868626371 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209571059/400000000 : ℝ)^4247 ≤ (21332866255197/50000000000000 : ℝ)^3223 := by
    have hnat : (209571059 : ℕ)^4247*50000000000000^3223 ≤ 21332866255197^3223*400000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209571059 400000000 21332866255197 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214033121/400000000 : ℝ), (-272982737/1250000000 : ℝ), (209571059/400000000 : ℝ)] ![(10966698242599/25000000000000 : ℝ), (3366868626371/25000000000000 : ℝ), (21332866255197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214033121/400000000 : ℝ)|^4247 ≤ (10966698242599/25000000000000 : ℝ)^3223
        have hw : |(214033121/400000000 : ℝ)|=(214033121/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272982737/1250000000 : ℝ)|^4247 ≤ (3366868626371/25000000000000 : ℝ)^3223
        have hw : |(-272982737/1250000000 : ℝ)|=(272982737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209571059/400000000 : ℝ)|^4247 ≤ (21332866255197/50000000000000 : ℝ)^3223
        have hw : |(209571059/400000000 : ℝ)|=(209571059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675414027/5000000000 : ℝ)*x 0 + (2619638199/5000000000 : ℝ)*x 1 + (-2183861959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675414027/5000000000 : ℝ)^4247 ≤ (21933396641839/50000000000000 : ℝ)^3223 := by
    have hnat : (2675414027 : ℕ)^4247*50000000000000^3223 ≤ 21933396641839^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675414027 5000000000 21933396641839 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619638199/5000000000 : ℝ)^4247 ≤ (42665731684127/100000000000000 : ℝ)^3223 := by
    have hnat : (2619638199 : ℕ)^4247*100000000000000^3223 ≤ 42665731684127^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619638199 5000000000 42665731684127 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183861959/10000000000 : ℝ)^4247 ≤ (13467475017429/100000000000000 : ℝ)^3223 := by
    have hnat : (2183861959 : ℕ)^4247*100000000000000^3223 ≤ 13467475017429^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183861959 10000000000 13467475017429 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675414027/5000000000 : ℝ), (2619638199/5000000000 : ℝ), (-2183861959/10000000000 : ℝ)] ![(21933396641839/50000000000000 : ℝ), (42665731684127/100000000000000 : ℝ), (13467475017429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675414027/5000000000 : ℝ)|^4247 ≤ (21933396641839/50000000000000 : ℝ)^3223
        have hw : |(2675414027/5000000000 : ℝ)|=(2675414027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619638199/5000000000 : ℝ)|^4247 ≤ (42665731684127/100000000000000 : ℝ)^3223
        have hw : |(2619638199/5000000000 : ℝ)|=(2619638199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183861959/10000000000 : ℝ)|^4247 ≤ (13467475017429/100000000000000 : ℝ)^3223
        have hw : |(-2183861959/10000000000 : ℝ)|=(2183861959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340943261/10000000000 : ℝ)*x 0 + (1040011153/2500000000 : ℝ)*x 1 + (4529366497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340943261/10000000000 : ℝ)^4247 ≤ (3329957053723/10000000000000 : ℝ)^3223 := by
    have hnat : (4340943261 : ℕ)^4247*10000000000000^3223 ≤ 3329957053723^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340943261 10000000000 3329957053723 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040011153/2500000000 : ℝ)^4247 ≤ (15741610824943/50000000000000 : ℝ)^3223 := by
    have hnat : (1040011153 : ℕ)^4247*50000000000000^3223 ≤ 15741610824943^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040011153 2500000000 15741610824943 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529366497/10000000000 : ℝ)^4247 ≤ (3521720780029/10000000000000 : ℝ)^3223 := by
    have hnat : (4529366497 : ℕ)^4247*10000000000000^3223 ≤ 3521720780029^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529366497 10000000000 3521720780029 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340943261/10000000000 : ℝ), (1040011153/2500000000 : ℝ), (4529366497/10000000000 : ℝ)] ![(3329957053723/10000000000000 : ℝ), (15741610824943/50000000000000 : ℝ), (3521720780029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340943261/10000000000 : ℝ)|^4247 ≤ (3329957053723/10000000000000 : ℝ)^3223
        have hw : |(4340943261/10000000000 : ℝ)|=(4340943261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040011153/2500000000 : ℝ)|^4247 ≤ (15741610824943/50000000000000 : ℝ)^3223
        have hw : |(1040011153/2500000000 : ℝ)|=(1040011153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529366497/10000000000 : ℝ)|^4247 ≤ (3521720780029/10000000000000 : ℝ)^3223
        have hw : |(4529366497/10000000000 : ℝ)|=(4529366497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092021303/10000000000 : ℝ)*x 0 + (654993147/1250000000 : ℝ)*x 1 + (2709323059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092021303/10000000000 : ℝ)^4247 ≤ (6363100843009/50000000000000 : ℝ)^3223 := by
    have hnat : (2092021303 : ℕ)^4247*50000000000000^3223 ≤ 6363100843009^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092021303 10000000000 6363100843009 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654993147/1250000000 : ℝ)^4247 ≤ (5334113539413/12500000000000 : ℝ)^3223 := by
    have hnat : (654993147 : ℕ)^4247*12500000000000^3223 ≤ 5334113539413^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654993147 1250000000 5334113539413 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709323059/5000000000 : ℝ)^4247 ≤ (4460088998293/10000000000000 : ℝ)^3223 := by
    have hnat : (2709323059 : ℕ)^4247*10000000000000^3223 ≤ 4460088998293^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709323059 5000000000 4460088998293 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092021303/10000000000 : ℝ), (654993147/1250000000 : ℝ), (2709323059/5000000000 : ℝ)] ![(6363100843009/50000000000000 : ℝ), (5334113539413/12500000000000 : ℝ), (4460088998293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092021303/10000000000 : ℝ)|^4247 ≤ (6363100843009/50000000000000 : ℝ)^3223
        have hw : |(-2092021303/10000000000 : ℝ)|=(2092021303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654993147/1250000000 : ℝ)|^4247 ≤ (5334113539413/12500000000000 : ℝ)^3223
        have hw : |(654993147/1250000000 : ℝ)|=(654993147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709323059/5000000000 : ℝ)|^4247 ≤ (4460088998293/10000000000000 : ℝ)^3223
        have hw : |(2709323059/5000000000 : ℝ)|=(2709323059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652380791/5000000000 : ℝ)*x 0 + (-400898463/2000000000 : ℝ)*x 1 + (1083729213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652380791/5000000000 : ℝ)^4247 ≤ (867396555113/2000000000000 : ℝ)^3223 := by
    have hnat : (2652380791 : ℕ)^4247*2000000000000^3223 ≤ 867396555113^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652380791 5000000000 867396555113 2000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400898463/2000000000 : ℝ)^4247 ≤ (6014641409139/50000000000000 : ℝ)^3223 := by
    have hnat : (400898463 : ℕ)^4247*50000000000000^3223 ≤ 6014641409139^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400898463 2000000000 6014641409139 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083729213/2000000000 : ℝ)^4247 ≤ (22300444704043/50000000000000 : ℝ)^3223 := by
    have hnat : (1083729213 : ℕ)^4247*50000000000000^3223 ≤ 22300444704043^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083729213 2000000000 22300444704043 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652380791/5000000000 : ℝ), (-400898463/2000000000 : ℝ), (1083729213/2000000000 : ℝ)] ![(867396555113/2000000000000 : ℝ), (6014641409139/50000000000000 : ℝ), (22300444704043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652380791/5000000000 : ℝ)|^4247 ≤ (867396555113/2000000000000 : ℝ)^3223
        have hw : |(2652380791/5000000000 : ℝ)|=(2652380791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400898463/2000000000 : ℝ)|^4247 ≤ (6014641409139/50000000000000 : ℝ)^3223
        have hw : |(-400898463/2000000000 : ℝ)|=(400898463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083729213/2000000000 : ℝ)|^4247 ≤ (22300444704043/50000000000000 : ℝ)^3223
        have hw : |(1083729213/2000000000 : ℝ)|=(1083729213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652380799/5000000000 : ℝ)*x 0 + (1083729223/2000000000 : ℝ)*x 1 + (-1002246113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652380799/5000000000 : ℝ)^4247 ≤ (2168491396401/5000000000000 : ℝ)^3223 := by
    have hnat : (2652380799 : ℕ)^4247*5000000000000^3223 ≤ 2168491396401^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652380799 5000000000 2168491396401 5000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083729223/2000000000 : ℝ)^4247 ≤ (5575111243799/12500000000000 : ℝ)^3223 := by
    have hnat : (1083729223 : ℕ)^4247*12500000000000^3223 ≤ 5575111243799^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083729223 2000000000 5575111243799 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002246113/5000000000 : ℝ)^4247 ≤ (12029282114481/100000000000000 : ℝ)^3223 := by
    have hnat : (1002246113 : ℕ)^4247*100000000000000^3223 ≤ 12029282114481^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002246113 5000000000 12029282114481 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652380799/5000000000 : ℝ), (1083729223/2000000000 : ℝ), (-1002246113/5000000000 : ℝ)] ![(2168491396401/5000000000000 : ℝ), (5575111243799/12500000000000 : ℝ), (12029282114481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652380799/5000000000 : ℝ)|^4247 ≤ (2168491396401/5000000000000 : ℝ)^3223
        have hw : |(2652380799/5000000000 : ℝ)|=(2652380799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083729223/2000000000 : ℝ)|^4247 ≤ (5575111243799/12500000000000 : ℝ)^3223
        have hw : |(1083729223/2000000000 : ℝ)|=(1083729223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002246113/5000000000 : ℝ)|^4247 ≤ (12029282114481/100000000000000 : ℝ)^3223
        have hw : |(-1002246113/5000000000 : ℝ)|=(1002246113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s4_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340972753/10000000000 : ℝ)*x 0 + (2263997523/5000000000 : ℝ)*x 1 + (832284719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340972753/10000000000 : ℝ)^4247 ≤ (16649934325203/50000000000000 : ℝ)^3223 := by
    have hnat : (4340972753 : ℕ)^4247*50000000000000^3223 ≤ 16649934325203^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340972753 10000000000 16649934325203 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263997523/5000000000 : ℝ)^4247 ≤ (35203157072643/100000000000000 : ℝ)^3223 := by
    have hnat : (2263997523 : ℕ)^4247*100000000000000^3223 ≤ 35203157072643^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263997523 5000000000 35203157072643 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832284719/2000000000 : ℝ)^4247 ≤ (31496974253123/100000000000000 : ℝ)^3223 := by
    have hnat : (832284719 : ℕ)^4247*100000000000000^3223 ≤ 31496974253123^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832284719 2000000000 31496974253123 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340972753/10000000000 : ℝ), (2263997523/5000000000 : ℝ), (832284719/2000000000 : ℝ)] ![(16649934325203/50000000000000 : ℝ), (35203157072643/100000000000000 : ℝ), (31496974253123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340972753/10000000000 : ℝ)|^4247 ≤ (16649934325203/50000000000000 : ℝ)^3223
        have hw : |(4340972753/10000000000 : ℝ)|=(4340972753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263997523/5000000000 : ℝ)|^4247 ≤ (35203157072643/100000000000000 : ℝ)^3223
        have hw : |(2263997523/5000000000 : ℝ)|=(2263997523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832284719/2000000000 : ℝ)|^4247 ≤ (31496974253123/100000000000000 : ℝ)^3223
        have hw : |(832284719/2000000000 : ℝ)|=(832284719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2659/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2659/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2659/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2659/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2659/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2659/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2659/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2659/25000 : ℝ) ^ (2123/512 : ℝ) ≤ (9216192691568199/100000000000000000000 : ℝ) := by
    have hpowers : (2659/25000 : ℝ)^2123 ≤ (9216192691568199/100000000000000000000 : ℝ)^512 := by
      have hnat : (2659 : ℕ)^2123*100000000000000000000^512 ≤ 9216192691568199^512*25000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2659 25000 9216192691568199 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2659/25000 : ℝ)) (X := (9216192691568199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15073/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (9780428934885037/25000000000000000000 : ℝ) := by
    have hpowers : (15073/100000 : ℝ)^2123 ≤ (9780428934885037/25000000000000000000 : ℝ)^512 := by
      have hnat : (15073 : ℕ)^2123*25000000000000000000^512 ≤ 9780428934885037^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15073 100000 9780428934885037 25000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15073/100000 : ℝ)) (X := (9780428934885037/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009216192691568199/50000000000000000000 : ℝ) ≤ (5000222249679237/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50009216192691568199/50000000000000000000 : ℝ)^512 ≤ (5000222249679237/5000000000000000 : ℝ)^2123 := by
      have hnat : (50009216192691568199 : ℕ)^512*5000000000000000^2123 ≤ 5000222249679237^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009216192691568199 50000000000000000000 5000222249679237 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000222249679237/5000000000000000 : ℝ)) (X := (50009216192691568199/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048337908431108347/100000000000000000000 : ℝ) ≤ (5000582771346957/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (100048337908431108347/100000000000000000000 : ℝ)^512 ≤ (5000582771346957/5000000000000000 : ℝ)^2123 := by
      have hnat : (100048337908431108347 : ℕ)^512*5000000000000000^2123 ≤ 5000582771346957^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048337908431108347 100000000000000000000 5000582771346957 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000582771346957/5000000000000000 : ℝ)) (X := (100048337908431108347/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509780428934885037/12500000000000000000 : ℝ) ≤ (5000943293014677/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (12509780428934885037/12500000000000000000 : ℝ)^512 ≤ (5000943293014677/5000000000000000 : ℝ)^2123 := by
      have hnat : (12509780428934885037 : ℕ)^512*5000000000000000^2123 ≤ 5000943293014677^2123*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509780428934885037 12500000000000000000 5000943293014677 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000943293014677/5000000000000000 : ℝ)) (X := (12509780428934885037/12500000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9216192691568199/100000000000000000000 : ℝ) ≤ ((2464257456101226081/2465000000000000000 : ℝ)+2*(1001449077/616250000000 : ℝ)*(2659/25000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (2464257456101226081/2465000000000000000 : ℝ)+2*(1001449077/616250000000 : ℝ)*(2659/25000 : ℝ)=(5000222249679237/5000000000000000 : ℝ) by norm_num, show 1+2*(9216192691568199/100000000000000000000 : ℝ)=(50009216192691568199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9780428934885037/25000000000000000000 : ℝ)+(9216192691568199/100000000000000000000 : ℝ) ≤ ((2464257456101226081/2465000000000000000 : ℝ)+(1001449077/616250000000 : ℝ)*((15073/100000 : ℝ)+(2659/25000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (2464257456101226081/2465000000000000000 : ℝ)+(1001449077/616250000000 : ℝ)*((15073/100000 : ℝ)+(2659/25000 : ℝ))=(5000582771346957/5000000000000000 : ℝ) by norm_num, show 1+(9780428934885037/25000000000000000000 : ℝ)+(9216192691568199/100000000000000000000 : ℝ)=(100048337908431108347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9780428934885037/25000000000000000000 : ℝ) ≤ ((2464257456101226081/2465000000000000000 : ℝ)+2*(1001449077/616250000000 : ℝ)*(15073/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (2464257456101226081/2465000000000000000 : ℝ)+2*(1001449077/616250000000 : ℝ)*(15073/100000 : ℝ)=(5000943293014677/5000000000000000 : ℝ) by norm_num, show 1+2*(9780428934885037/25000000000000000000 : ℝ)=(12509780428934885037/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2464257456101226081/2465000000000000000 : ℝ)*(X 1 0+X 2 0)+(1001449077/616250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2659/25000 : ℝ)) (hi := (15073/100000 : ℝ)) (c := (2464257456101226081/2465000000000000000 : ℝ)) (alpha := (1001449077/616250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2464257456101226081/2465000000000000000 : ℝ)*(X 0 1+X 2 1)+(1001449077/616250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2659/25000 : ℝ)) (hi := (15073/100000 : ℝ)) (c := (2464257456101226081/2465000000000000000 : ℝ)) (alpha := (1001449077/616250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2464257456101226081/2465000000000000000 : ℝ)*(X 0 2+X 1 2)+(1001449077/616250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2659/25000 : ℝ)) (hi := (15073/100000 : ℝ)) (c := (2464257456101226081/2465000000000000000 : ℝ)) (alpha := (1001449077/616250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2092007001/10000000000 : ℝ)*X 0 0+(2709659097/5000000000 : ℝ)*X 0 1+(5239276557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214033121/400000000 : ℝ)*X 1 0+(-272982737/1250000000 : ℝ)*X 1 1+(209571059/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675414027/5000000000 : ℝ)*X 2 0+(2619638199/5000000000 : ℝ)*X 2 1+(-2183861959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340943261/10000000000 : ℝ)*X 0 0+(1040011153/2500000000 : ℝ)*X 0 1+(4529366497/10000000000 : ℝ)*X 0 2+(4340943261/10000000000 : ℝ)*X 1 0+(1040011153/2500000000 : ℝ)*X 1 1+(4529366497/10000000000 : ℝ)*X 1 2+(4340943261/10000000000 : ℝ)*X 2 0+(1040011153/2500000000 : ℝ)*X 2 1+(4529366497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092021303/10000000000 : ℝ)*X 0 0+(654993147/1250000000 : ℝ)*X 0 1+(2709323059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652380791/5000000000 : ℝ)*X 1 0+(-400898463/2000000000 : ℝ)*X 1 1+(1083729213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652380799/5000000000 : ℝ)*X 2 0+(1083729223/2000000000 : ℝ)*X 2 1+(-1002246113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340972753/10000000000 : ℝ)*X 0 0+(2263997523/5000000000 : ℝ)*X 0 1+(832284719/2000000000 : ℝ)*X 0 2+(4340972753/10000000000 : ℝ)*X 1 0+(2263997523/5000000000 : ℝ)*X 1 1+(832284719/2000000000 : ℝ)*X 1 2+(4340972753/10000000000 : ℝ)*X 2 0+(2263997523/5000000000 : ℝ)*X 2 1+(832284719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (441947283303223367577370647/61625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (450177157/25000000000000 : ℝ)*(base19) + (1809504483/100000000000000 : ℝ)*(base23) + (31303/12500000000 : ℝ)*(upper3) + (11401057/100000000000000 : ℝ)*(upper4) + (168078181/100000000000000 : ℝ)*(upper5) + (2065508973671229/50000000000000 : ℝ)*(major0) + (2065508973671229/50000000000000 : ℝ)*(major1) + (2065508973671229/50000000000000 : ℝ)*(major2) + (1110860850156083/20000000000000 : ℝ)*(sp0) + (1110866748579489/20000000000000 : ℝ)*(sp1) + (5554333734101589/100000000000000 : ℝ)*(sp2) + (270768189996827/10000000000000 : ℝ)*(sp3) + (31292825657/100000000000000 : ℝ)*(sp4) + (9106029311/50000000000000 : ℝ)*(sp7) + (2707700112026891/100000000000000 : ℝ)*(f.failure) + (694291942950759/12500000000000 : ℝ)*(f.sum) + (1723984103147/246500000000000000000000000 : ℝ)*base66 + (307523308784376451/123250000000000000000000000000000 : ℝ)*base68 + (158470401782873549/123250000000000000000000000000000 : ℝ)*base69 + (1729994938717126451/123250000000000000000000000000000 : ℝ)*base72 + (4344417041/24650000000000000000000000 : ℝ)*base74 + (1950093765002626451/123250000000000000000000000000000 : ℝ)*base76 + (1175404655900376451/123250000000000000000000000000000 : ℝ)*base78 + (127864060455623549/123250000000000000000000000000000 : ℝ)*base79 + (3866074150241/493000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2145381/2500000000000000000000 : ℝ)*base89 + (2145381/2500000000000000000000 : ℝ)*base91 + (2145381/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10627669988598731908140117/2125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64379749/6250000000000 : ℝ)*(base19) + (558658729/50000000000000 : ℝ)*(base23) + (57519757/50000000000000 : ℝ)*(upper3) + (1880831/12500000000000 : ℝ)*(lower4) + (68104649/100000000000000 : ℝ)*(upper5) + (2080980467837983/50000000000000 : ℝ)*(major0) + (2080980467837983/50000000000000 : ℝ)*(major1) + (2080980467837983/50000000000000 : ℝ)*(major2) + (18242572343/100000000000000 : ℝ)*(sp1) + (11539461001/50000000000000 : ℝ)*(sp2) + (44767518625273/800000000000 : ℝ)*(sp4) + (2797960277755399/50000000000000 : ℝ)*(sp5) + (349744726994979/6250000000000 : ℝ)*(sp6) + (34099773456053/1250000000000 : ℝ)*(sp7) + (34099773456053/1250000000000 : ℝ)*(f.failure) + (44767518625273/800000000000 : ℝ)*(f.sum) + (12752159363/17000000000000000000000000 : ℝ)*base65 + (72072813996414987/4250000000000000000000000000000 : ℝ)*base67 + (29762944078914987/4250000000000000000000000000000 : ℝ)*base69 + (34945741809664987/4250000000000000000000000000000 : ℝ)*base71 + (59710668457/8500000000000000000000000 : ℝ)*base73 + (72068659387664987/4250000000000000000000000000000 : ℝ)*base75 + (33429205091414987/4250000000000000000000000000000 : ℝ)*base77 + (39419710583414987/4250000000000000000000000000000 : ℝ)*base79 + (33073406089/8500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (585277/31250000000000000000 : ℝ)*base90 + (585277/31250000000000000000 : ℝ)*base92 + (585277/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2659/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s5_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092380859/10000000000 : ℝ)*x 0 + (1083234809/2000000000 : ℝ)*x 1 + (524217481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092380859/10000000000 : ℝ)^4247 ≤ (2545816789067/20000000000000 : ℝ)^3223 := by
    have hnat : (2092380859 : ℕ)^4247*20000000000000^3223 ≤ 2545816789067^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092380859 10000000000 2545816789067 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083234809/2000000000 : ℝ)^4247 ≤ (44574079508243/100000000000000 : ℝ)^3223 := by
    have hnat : (1083234809 : ℕ)^4247*100000000000000^3223 ≤ 44574079508243^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083234809 2000000000 44574079508243 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524217481/1000000000 : ℝ)^4247 ≤ (21348418267453/50000000000000 : ℝ)^3223 := by
    have hnat : (524217481 : ℕ)^4247*50000000000000^3223 ≤ 21348418267453^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524217481 1000000000 21348418267453 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092380859/10000000000 : ℝ), (1083234809/2000000000 : ℝ), (524217481/1000000000 : ℝ)] ![(2545816789067/20000000000000 : ℝ), (44574079508243/100000000000000 : ℝ), (21348418267453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092380859/10000000000 : ℝ)|^4247 ≤ (2545816789067/20000000000000 : ℝ)^3223
        have hw : |(-2092380859/10000000000 : ℝ)|=(2092380859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083234809/2000000000 : ℝ)|^4247 ≤ (44574079508243/100000000000000 : ℝ)^3223
        have hw : |(1083234809/2000000000 : ℝ)|=(1083234809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524217481/1000000000 : ℝ)|^4247 ≤ (21348418267453/50000000000000 : ℝ)^3223
        have hw : |(524217481/1000000000 : ℝ)|=(524217481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668753829/1250000000 : ℝ)*x 0 + (-2181093717/10000000000 : ℝ)*x 1 + (5242174797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668753829/1250000000 : ℝ)^4247 ≤ (21929089543539/50000000000000 : ℝ)^3223 := by
    have hnat : (668753829 : ℕ)^4247*50000000000000^3223 ≤ 21929089543539^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668753829 1250000000 21929089543539 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181093717/10000000000 : ℝ)^4247 ≤ (13444984496353/100000000000000 : ℝ)^3223 := by
    have hnat : (2181093717 : ℕ)^4247*100000000000000^3223 ≤ 13444984496353^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181093717 10000000000 13444984496353 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242174797/10000000000 : ℝ)^4247 ≤ (21348418197691/50000000000000 : ℝ)^3223 := by
    have hnat : (5242174797 : ℕ)^4247*50000000000000^3223 ≤ 21348418197691^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242174797 10000000000 21348418197691 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668753829/1250000000 : ℝ), (-2181093717/10000000000 : ℝ), (5242174797/10000000000 : ℝ)] ![(21929089543539/50000000000000 : ℝ), (13444984496353/100000000000000 : ℝ), (21348418197691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668753829/1250000000 : ℝ)|^4247 ≤ (21929089543539/50000000000000 : ℝ)^3223
        have hw : |(668753829/1250000000 : ℝ)|=(668753829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181093717/10000000000 : ℝ)|^4247 ≤ (13444984496353/100000000000000 : ℝ)^3223
        have hw : |(-2181093717/10000000000 : ℝ)|=(2181093717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242174797/10000000000 : ℝ)|^4247 ≤ (21348418197691/50000000000000 : ℝ)^3223
        have hw : |(5242174797/10000000000 : ℝ)|=(5242174797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535003061/1000000000 : ℝ)*x 0 + (2621087413/5000000000 : ℝ)*x 1 + (-545273427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535003061/1000000000 : ℝ)^4247 ≤ (10964544712357/25000000000000 : ℝ)^3223 := by
    have hnat : (535003061 : ℕ)^4247*25000000000000^3223 ≤ 10964544712357^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535003061 1000000000 10964544712357 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621087413/5000000000 : ℝ)^4247 ≤ (10674209176657/25000000000000 : ℝ)^3223 := by
    have hnat : (2621087413 : ℕ)^4247*25000000000000^3223 ≤ 10674209176657^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621087413 5000000000 10674209176657 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545273427/2500000000 : ℝ)^4247 ≤ (13444984423247/100000000000000 : ℝ)^3223 := by
    have hnat : (545273427 : ℕ)^4247*100000000000000^3223 ≤ 13444984423247^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545273427 2500000000 13444984423247 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535003061/1000000000 : ℝ), (2621087413/5000000000 : ℝ), (-545273427/2500000000 : ℝ)] ![(10964544712357/25000000000000 : ℝ), (10674209176657/25000000000000 : ℝ), (13444984423247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535003061/1000000000 : ℝ)|^4247 ≤ (10964544712357/25000000000000 : ℝ)^3223
        have hw : |(535003061/1000000000 : ℝ)|=(535003061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621087413/5000000000 : ℝ)|^4247 ≤ (10674209176657/25000000000000 : ℝ)^3223
        have hw : |(2621087413/5000000000 : ℝ)|=(2621087413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545273427/2500000000 : ℝ)|^4247 ≤ (13444984423247/100000000000000 : ℝ)^3223
        have hw : |(-545273427/2500000000 : ℝ)|=(545273427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434116333/1000000000 : ℝ)*x 0 + (1041553647/2500000000 : ℝ)*x 1 + (452314113/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434116333/1000000000 : ℝ)^4247 ≤ (8325448767549/25000000000000 : ℝ)^3223 := by
    have hnat : (434116333 : ℕ)^4247*25000000000000^3223 ≤ 8325448767549^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434116333 1000000000 8325448767549 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041553647/2500000000 : ℝ)^4247 ≤ (7886191524693/25000000000000 : ℝ)^3223 := by
    have hnat : (1041553647 : ℕ)^4247*25000000000000^3223 ≤ 7886191524693^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041553647 2500000000 7886191524693 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452314113/1000000000 : ℝ)^4247 ≤ (17576719407493/50000000000000 : ℝ)^3223 := by
    have hnat : (452314113 : ℕ)^4247*50000000000000^3223 ≤ 17576719407493^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452314113 1000000000 17576719407493 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434116333/1000000000 : ℝ), (1041553647/2500000000 : ℝ), (452314113/1000000000 : ℝ)] ![(8325448767549/25000000000000 : ℝ), (7886191524693/25000000000000 : ℝ), (17576719407493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434116333/1000000000 : ℝ)|^4247 ≤ (8325448767549/25000000000000 : ℝ)^3223
        have hw : |(434116333/1000000000 : ℝ)|=(434116333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041553647/2500000000 : ℝ)|^4247 ≤ (7886191524693/25000000000000 : ℝ)^3223
        have hw : |(1041553647/2500000000 : ℝ)|=(1041553647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452314113/1000000000 : ℝ)|^4247 ≤ (17576719407493/50000000000000 : ℝ)^3223
        have hw : |(452314113/1000000000 : ℝ)|=(452314113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092393943/10000000000 : ℝ)*x 0 + (5242799453/10000000000 : ℝ)*x 1 + (2707773077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092393943/10000000000 : ℝ)^4247 ≤ (12729188831773/100000000000000 : ℝ)^3223 := by
    have hnat : (2092393943 : ℕ)^4247*100000000000000^3223 ≤ 12729188831773^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092393943 10000000000 12729188831773 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242799453/10000000000 : ℝ)^4247 ≤ (21351770361983/50000000000000 : ℝ)^3223 := by
    have hnat : (5242799453 : ℕ)^4247*50000000000000^3223 ≤ 21351770361983^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242799453 10000000000 21351770361983 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707773077/5000000000 : ℝ)^4247 ≤ (1392727201103/3125000000000 : ℝ)^3223 := by
    have hnat : (2707773077 : ℕ)^4247*3125000000000^3223 ≤ 1392727201103^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707773077 5000000000 1392727201103 3125000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092393943/10000000000 : ℝ), (5242799453/10000000000 : ℝ), (2707773077/5000000000 : ℝ)] ![(12729188831773/100000000000000 : ℝ), (21351770361983/50000000000000 : ℝ), (1392727201103/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092393943/10000000000 : ℝ)|^4247 ≤ (12729188831773/100000000000000 : ℝ)^3223
        have hw : |(-2092393943/10000000000 : ℝ)|=(2092393943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242799453/10000000000 : ℝ)|^4247 ≤ (21351770361983/50000000000000 : ℝ)^3223
        have hw : |(5242799453/10000000000 : ℝ)|=(5242799453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707773077/5000000000 : ℝ)|^4247 ≤ (1392727201103/3125000000000 : ℝ)^3223
        have hw : |(2707773077/5000000000 : ℝ)|=(2707773077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326377653/2500000000 : ℝ)*x 0 + (-125482649/625000000 : ℝ)*x 1 + (2707773077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326377653/2500000000 : ℝ)^4247 ≤ (43377897369191/100000000000000 : ℝ)^3223 := by
    have hnat : (1326377653 : ℕ)^4247*100000000000000^3223 ≤ 43377897369191^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326377653 2500000000 43377897369191 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125482649/625000000 : ℝ)^4247 ≤ (6027416094673/50000000000000 : ℝ)^3223 := by
    have hnat : (125482649 : ℕ)^4247*50000000000000^3223 ≤ 6027416094673^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125482649 625000000 6027416094673 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707773077/5000000000 : ℝ)^4247 ≤ (1392727201103/3125000000000 : ℝ)^3223 := by
    have hnat : (2707773077 : ℕ)^4247*3125000000000^3223 ≤ 1392727201103^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707773077 5000000000 1392727201103 3125000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326377653/2500000000 : ℝ), (-125482649/625000000 : ℝ), (2707773077/5000000000 : ℝ)] ![(43377897369191/100000000000000 : ℝ), (6027416094673/50000000000000 : ℝ), (1392727201103/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326377653/2500000000 : ℝ)|^4247 ≤ (43377897369191/100000000000000 : ℝ)^3223
        have hw : |(1326377653/2500000000 : ℝ)|=(1326377653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125482649/625000000 : ℝ)|^4247 ≤ (6027416094673/50000000000000 : ℝ)^3223
        have hw : |(-125482649/625000000 : ℝ)|=(125482649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707773077/5000000000 : ℝ)|^4247 ≤ (1392727201103/3125000000000 : ℝ)^3223
        have hw : |(2707773077/5000000000 : ℝ)|=(2707773077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326377653/2500000000 : ℝ)*x 0 + (5415546153/10000000000 : ℝ)*x 1 + (-2007722383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326377653/2500000000 : ℝ)^4247 ≤ (43377897369191/100000000000000 : ℝ)^3223 := by
    have hnat : (1326377653 : ℕ)^4247*100000000000000^3223 ≤ 43377897369191^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326377653 2500000000 43377897369191 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415546153/10000000000 : ℝ)^4247 ≤ (11141817606113/25000000000000 : ℝ)^3223 := by
    have hnat : (5415546153 : ℕ)^4247*25000000000000^3223 ≤ 11141817606113^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415546153 10000000000 11141817606113 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007722383/10000000000 : ℝ)^4247 ≤ (2410966436287/20000000000000 : ℝ)^3223 := by
    have hnat : (2007722383 : ℕ)^4247*20000000000000^3223 ≤ 2410966436287^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007722383 10000000000 2410966436287 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326377653/2500000000 : ℝ), (5415546153/10000000000 : ℝ), (-2007722383/10000000000 : ℝ)] ![(43377897369191/100000000000000 : ℝ), (11141817606113/25000000000000 : ℝ), (2410966436287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326377653/2500000000 : ℝ)|^4247 ≤ (43377897369191/100000000000000 : ℝ)^3223
        have hw : |(1326377653/2500000000 : ℝ)|=(1326377653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415546153/10000000000 : ℝ)|^4247 ≤ (11141817606113/25000000000000 : ℝ)^3223
        have hw : |(5415546153/10000000000 : ℝ)|=(5415546153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2007722383/10000000000 : ℝ)|^4247 ≤ (2410966436287/20000000000000 : ℝ)^3223
        have hw : |(-2007722383/10000000000 : ℝ)|=(2007722383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s5_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341190223/10000000000 : ℝ)*x 0 + (1130464939/2500000000 : ℝ)*x 1 + (2083751249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341190223/10000000000 : ℝ)^4247 ≤ (1332082676653/4000000000000 : ℝ)^3223 := by
    have hnat : (4341190223 : ℕ)^4247*4000000000000^3223 ≤ 1332082676653^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341190223 10000000000 1332082676653 4000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130464939/2500000000 : ℝ)^4247 ≤ (8785079158727/25000000000000 : ℝ)^3223 := by
    have hnat : (1130464939 : ℕ)^4247*25000000000000^3223 ≤ 8785079158727^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130464939 2500000000 8785079158727 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083751249/5000000000 : ℝ)^4247 ≤ (15778808217223/50000000000000 : ℝ)^3223 := by
    have hnat : (2083751249 : ℕ)^4247*50000000000000^3223 ≤ 15778808217223^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083751249 5000000000 15778808217223 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341190223/10000000000 : ℝ), (1130464939/2500000000 : ℝ), (2083751249/5000000000 : ℝ)] ![(1332082676653/4000000000000 : ℝ), (8785079158727/25000000000000 : ℝ), (15778808217223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341190223/10000000000 : ℝ)|^4247 ≤ (1332082676653/4000000000000 : ℝ)^3223
        have hw : |(4341190223/10000000000 : ℝ)|=(4341190223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130464939/2500000000 : ℝ)|^4247 ≤ (8785079158727/25000000000000 : ℝ)^3223
        have hw : |(1130464939/2500000000 : ℝ)|=(1130464939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083751249/5000000000 : ℝ)|^4247 ≤ (15778808217223/50000000000000 : ℝ)^3223
        have hw : |(2083751249/5000000000 : ℝ)|=(2083751249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10939/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (10354657228827411/100000000000000000000 : ℝ) := by
    have hpowers : (10939/100000 : ℝ)^2123 ≤ (10354657228827411/100000000000000000000 : ℝ)^512 := by
      have hnat : (10939 : ℕ)^2123*100000000000000000000^512 ≤ 10354657228827411^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10939 100000 10354657228827411 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10939/100000 : ℝ)) (X := (10354657228827411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (8937725588907947/25000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^2123 ≤ (8937725588907947/25000000000000000000 : ℝ)^512 := by
      have hnat : (14749 : ℕ)^2123*25000000000000000000^512 ≤ 8937725588907947^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 8937725588907947 25000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (8937725588907947/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010354657228827411/50000000000000000000 : ℝ) ≤ (5000249701742003/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50010354657228827411/50000000000000000000 : ℝ)^512 ≤ (5000249701742003/5000000000000000 : ℝ)^2123 := by
      have hnat : (50010354657228827411 : ℕ)^512*5000000000000000^2123 ≤ 5000249701742003^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010354657228827411 50000000000000000000 5000249701742003 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000249701742003/5000000000000000 : ℝ)) (X := (50010354657228827411/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046105559584459199/100000000000000000000 : ℝ) ≤ (2000222344966313/2000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (100046105559584459199/100000000000000000000 : ℝ)^512 ≤ (2000222344966313/2000000000000000 : ℝ)^2123 := by
      have hnat : (100046105559584459199 : ℕ)^512*2000000000000000^2123 ≤ 2000222344966313^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046105559584459199 100000000000000000000 2000222344966313 2000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222344966313/2000000000000000 : ℝ)) (X := (100046105559584459199/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508937725588907947/12500000000000000000 : ℝ) ≤ (2500431011544781/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (12508937725588907947/12500000000000000000 : ℝ)^512 ≤ (2500431011544781/2500000000000000 : ℝ)^2123 := by
      have hnat : (12508937725588907947 : ℕ)^512*2500000000000000^2123 ≤ 2500431011544781^2123*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508937725588907947 12500000000000000000 2500431011544781 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500431011544781/2500000000000000 : ℝ)) (X := (12508937725588907947/12500000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10354657228827411/100000000000000000000 : ℝ) ≤ ((6348084393472027843/6350000000000000000 : ℝ)+2*(204107115853/127000000000000 : ℝ)*(10939/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (6348084393472027843/6350000000000000000 : ℝ)+2*(204107115853/127000000000000 : ℝ)*(10939/100000 : ℝ)=(5000249701742003/5000000000000000 : ℝ) by norm_num, show 1+2*(10354657228827411/100000000000000000000 : ℝ)=(50010354657228827411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8937725588907947/25000000000000000000 : ℝ)+(10354657228827411/100000000000000000000 : ℝ) ≤ ((6348084393472027843/6350000000000000000 : ℝ)+(204107115853/127000000000000 : ℝ)*((14749/100000 : ℝ)+(10939/100000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (6348084393472027843/6350000000000000000 : ℝ)+(204107115853/127000000000000 : ℝ)*((14749/100000 : ℝ)+(10939/100000 : ℝ))=(2000222344966313/2000000000000000 : ℝ) by norm_num, show 1+(8937725588907947/25000000000000000000 : ℝ)+(10354657228827411/100000000000000000000 : ℝ)=(100046105559584459199/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8937725588907947/25000000000000000000 : ℝ) ≤ ((6348084393472027843/6350000000000000000 : ℝ)+2*(204107115853/127000000000000 : ℝ)*(14749/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (6348084393472027843/6350000000000000000 : ℝ)+2*(204107115853/127000000000000 : ℝ)*(14749/100000 : ℝ)=(2500431011544781/2500000000000000 : ℝ) by norm_num, show 1+2*(8937725588907947/25000000000000000000 : ℝ)=(12508937725588907947/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6348084393472027843/6350000000000000000 : ℝ)*(X 1 0+X 2 0)+(204107115853/127000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6348084393472027843/6350000000000000000 : ℝ)) (alpha := (204107115853/127000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6348084393472027843/6350000000000000000 : ℝ)*(X 0 1+X 2 1)+(204107115853/127000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6348084393472027843/6350000000000000000 : ℝ)) (alpha := (204107115853/127000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6348084393472027843/6350000000000000000 : ℝ)*(X 0 2+X 1 2)+(204107115853/127000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6348084393472027843/6350000000000000000 : ℝ)) (alpha := (204107115853/127000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2092380859/10000000000 : ℝ)*X 0 0+(1083234809/2000000000 : ℝ)*X 0 1+(524217481/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668753829/1250000000 : ℝ)*X 1 0+(-2181093717/10000000000 : ℝ)*X 1 1+(5242174797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535003061/1000000000 : ℝ)*X 2 0+(2621087413/5000000000 : ℝ)*X 2 1+(-545273427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434116333/1000000000 : ℝ)*X 0 0+(1041553647/2500000000 : ℝ)*X 0 1+(452314113/1000000000 : ℝ)*X 0 2+(434116333/1000000000 : ℝ)*X 1 0+(1041553647/2500000000 : ℝ)*X 1 1+(452314113/1000000000 : ℝ)*X 1 2+(434116333/1000000000 : ℝ)*X 2 0+(1041553647/2500000000 : ℝ)*X 2 1+(452314113/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092393943/10000000000 : ℝ)*X 0 0+(5242799453/10000000000 : ℝ)*X 0 1+(2707773077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326377653/2500000000 : ℝ)*X 1 0+(-125482649/625000000 : ℝ)*X 1 1+(2707773077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326377653/2500000000 : ℝ)*X 2 0+(5415546153/10000000000 : ℝ)*X 2 1+(-2007722383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341190223/10000000000 : ℝ)*X 0 0+(1130464939/2500000000 : ℝ)*X 0 1+(2083751249/5000000000 : ℝ)*X 0 2+(4341190223/10000000000 : ℝ)*X 1 0+(1130464939/2500000000 : ℝ)*X 1 1+(2083751249/5000000000 : ℝ)*X 1 2+(4341190223/10000000000 : ℝ)*X 2 0+(1130464939/2500000000 : ℝ)*X 2 1+(2083751249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (285433138652042211691121283/39687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41411451/3125000000000 : ℝ)*(base19) + (617742487/50000000000000 : ℝ)*(base23) + (17668001/50000000000000 : ℝ)*(lower2) + (29658267/20000000000000 : ℝ)*(upper3) + (26361977/25000000000000 : ℝ)*(upper5) + (534308200230509/12500000000000 : ℝ)*(major0) + (534308200230509/12500000000000 : ℝ)*(major1) + (534308200230509/12500000000000 : ℝ)*(major2) + (5747179857392273/100000000000000 : ℝ)*(sp0) + (718400739299183/12500000000000 : ℝ)*(sp1) + (5747206004074923/100000000000000 : ℝ)*(sp2) + (1400854941511727/50000000000000 : ℝ)*(sp3) + (3422770953/12500000000000 : ℝ)*(sp4) + (13841370913/100000000000000 : ℝ)*(sp7) + (2801723724394367/100000000000000 : ℝ)*(f.failure) + (718400904944987/12500000000000 : ℝ)*(f.sum) + (3902374234427/793750000000000000000000000 : ℝ)*base65 + (1290457719149462913/79375000000000000000000000000000 : ℝ)*base68 + (403210063800087913/79375000000000000000000000000000 : ℝ)*base70 + (460110012468212913/79375000000000000000000000000000 : ℝ)*base72 + (621797950769/99218750000000000000000000 : ℝ)*base73 + (115599956871337913/79375000000000000000000000000000 : ℝ)*base76 + (514307562664462913/79375000000000000000000000000000 : ℝ)*base78 + (1552460659153837913/79375000000000000000000000000000 : ℝ)*base80 + (10695113322479/1587500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10055503/2500000000000000000000 : ℝ)*base90 + (10055503/2500000000000000000000 : ℝ)*base92 + (10055503/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3678554459945504128911/1587500000000000000000000000 : ℝ) := by norm_num
    linear_combination (82983121/20000000000000 : ℝ)*(base19) + (451104053/100000000000000 : ℝ)*(base23) + (23663881/50000000000000 : ℝ)*(upper3) + (16365609/100000000000000 : ℝ)*(lower4) + (47317861/100000000000000 : ℝ)*(upper5) + (269088532300249/6250000000000 : ℝ)*(major0) + (269088532300249/6250000000000 : ℝ)*(major1) + (269088532300249/6250000000000 : ℝ)*(major2) + (4120876243/50000000000000 : ℝ)*(sp1) + (2219592917/25000000000000 : ℝ)*(sp2) + (2894411135981081/50000000000000 : ℝ)*(sp4) + (723601701911759/12500000000000 : ℝ)*(sp5) + (2894406471243221/50000000000000 : ℝ)*(sp6) + (282201068440581/10000000000000 : ℝ)*(sp7) + (282201068440581/10000000000000 : ℝ)*(f.failure) + (2894411135981081/50000000000000 : ℝ)*(f.sum) + (295358064253/396875000000000000000000000 : ℝ)*base66 + (116019601814307907/39687500000000000000000000000000 : ℝ)*base67 + (323924214341182907/39687500000000000000000000000000 : ℝ)*base69 + (435127024966942093/39687500000000000000000000000000 : ℝ)*base72 + (3281770992713/1587500000000000000000000000 : ℝ)*base73 + (230401793225692093/39687500000000000000000000000000 : ℝ)*base76 + (375398796696942093/39687500000000000000000000000000 : ℝ)*base78 + (317684092121807907/39687500000000000000000000000000 : ℝ)*base79 + (7167855263963/1587500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (188171/250000000000000000000 : ℝ)*base89 + (188171/250000000000000000000 : ℝ)*base91 + (188171/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1287_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1287_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1287_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1287_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1287_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
