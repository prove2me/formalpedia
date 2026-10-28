-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:04:24.897207+00:00
-- url     : https://prove2.me/submissions/afbe1bb0-0dbe-432d-b0a7-c98d40402f8e

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
theorem support_rectangle_w1062_box_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2076139017/10000000000 : ℝ)*x 0 + (5377421597/10000000000 : ℝ)*x 1 + (5377423089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076139017/10000000000 : ℝ)^8255 ≤ (12359051755071/100000000000000 : ℝ)^6207 := by
    have hnat : (2076139017 : ℕ)^8255*100000000000000^6207 ≤ 12359051755071^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076139017 10000000000 12359051755071 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377421597/10000000000 : ℝ)^8255 ≤ (10955116506251/25000000000000 : ℝ)^6207 := by
    have hnat : (5377421597 : ℕ)^8255*25000000000000^6207 ≤ 10955116506251^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377421597 10000000000 10955116506251 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377423089/10000000000 : ℝ)^8255 ≤ (8764096438979/20000000000000 : ℝ)^6207 := by
    have hnat : (5377423089 : ℕ)^8255*20000000000000^6207 ≤ 8764096438979^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377423089 10000000000 8764096438979 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2076139017/10000000000 : ℝ), (5377421597/10000000000 : ℝ), (5377423089/10000000000 : ℝ)] ![(12359051755071/100000000000000 : ℝ), (10955116506251/25000000000000 : ℝ), (8764096438979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2076139017/10000000000 : ℝ)|^8255 ≤ (12359051755071/100000000000000 : ℝ)^6207
        have hw : |(-2076139017/10000000000 : ℝ)|=(2076139017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377421597/10000000000 : ℝ)|^8255 ≤ (10955116506251/25000000000000 : ℝ)^6207
        have hw : |(5377421597/10000000000 : ℝ)|=(5377421597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377423089/10000000000 : ℝ)|^8255 ≤ (8764096438979/20000000000000 : ℝ)^6207
        have hw : |(5377423089/10000000000 : ℝ)|=(5377423089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295156443/10000000000 : ℝ)*x 0 + (-2187494431/10000000000 : ℝ)*x 1 + (2688711183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295156443/10000000000 : ℝ)^8255 ≤ (1717246263393/4000000000000 : ℝ)^6207 := by
    have hnat : (5295156443 : ℕ)^8255*4000000000000^6207 ≤ 1717246263393^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295156443 10000000000 1717246263393 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187494431/10000000000 : ℝ)^8255 ≤ (3312092259111/25000000000000 : ℝ)^6207 := by
    have hnat : (2187494431 : ℕ)^8255*25000000000000^6207 ≤ 3312092259111^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187494431 10000000000 3312092259111 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688711183/5000000000 : ℝ)^8255 ≤ (43820474359217/100000000000000 : ℝ)^6207 := by
    have hnat : (2688711183 : ℕ)^8255*100000000000000^6207 ≤ 43820474359217^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688711183 5000000000 43820474359217 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295156443/10000000000 : ℝ), (-2187494431/10000000000 : ℝ), (2688711183/5000000000 : ℝ)] ![(1717246263393/4000000000000 : ℝ), (3312092259111/25000000000000 : ℝ), (43820474359217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295156443/10000000000 : ℝ)|^8255 ≤ (1717246263393/4000000000000 : ℝ)^6207
        have hw : |(5295156443/10000000000 : ℝ)|=(5295156443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187494431/10000000000 : ℝ)|^8255 ≤ (3312092259111/25000000000000 : ℝ)^6207
        have hw : |(-2187494431/10000000000 : ℝ)|=(2187494431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688711183/5000000000 : ℝ)|^8255 ≤ (43820474359217/100000000000000 : ℝ)^6207
        have hw : |(2688711183/5000000000 : ℝ)|=(2688711183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295156721/10000000000 : ℝ)*x 0 + (5377422761/10000000000 : ℝ)*x 1 + (-273436691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295156721/10000000000 : ℝ)^8255 ≤ (21465579791213/50000000000000 : ℝ)^6207 := by
    have hnat : (5295156721 : ℕ)^8255*50000000000000^6207 ≤ 21465579791213^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295156721 10000000000 21465579791213 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377422761/10000000000 : ℝ)^8255 ≤ (1095511966003/2500000000000 : ℝ)^6207 := by
    have hnat : (5377422761 : ℕ)^8255*2500000000000^6207 ≤ 1095511966003^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377422761 10000000000 1095511966003 2500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273436691/1250000000 : ℝ)^8255 ≤ (13248361763027/100000000000000 : ℝ)^6207 := by
    have hnat : (273436691 : ℕ)^8255*100000000000000^6207 ≤ 13248361763027^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273436691 1250000000 13248361763027 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295156721/10000000000 : ℝ), (5377422761/10000000000 : ℝ), (-273436691/1250000000 : ℝ)] ![(21465579791213/50000000000000 : ℝ), (1095511966003/2500000000000 : ℝ), (13248361763027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295156721/10000000000 : ℝ)|^8255 ≤ (21465579791213/50000000000000 : ℝ)^6207
        have hw : |(5295156721/10000000000 : ℝ)|=(5295156721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377422761/10000000000 : ℝ)|^8255 ≤ (1095511966003/2500000000000 : ℝ)^6207
        have hw : |(5377422761/10000000000 : ℝ)|=(5377422761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273436691/1250000000 : ℝ)|^8255 ≤ (13248361763027/100000000000000 : ℝ)^6207
        have hw : |(-273436691/1250000000 : ℝ)|=(273436691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (224225207/500000000 : ℝ)*x 0 + (2162008377/5000000000 : ℝ)*x 1 + (2162008393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224225207/500000000 : ℝ)^8255 ≤ (1720947373889/5000000000000 : ℝ)^6207 := by
    have hnat : (224225207 : ℕ)^8255*5000000000000^6207 ≤ 1720947373889^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224225207 500000000 1720947373889 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162008377/5000000000 : ℝ)^8255 ≤ (32790526092611/100000000000000 : ℝ)^6207 := by
    have hnat : (2162008377 : ℕ)^8255*100000000000000^6207 ≤ 32790526092611^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162008377 5000000000 32790526092611 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162008393/5000000000 : ℝ)^8255 ≤ (16395263207673/50000000000000 : ℝ)^6207 := by
    have hnat : (2162008393 : ℕ)^8255*50000000000000^6207 ≤ 16395263207673^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162008393 5000000000 16395263207673 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224225207/500000000 : ℝ), (2162008377/5000000000 : ℝ), (2162008393/5000000000 : ℝ)] ![(1720947373889/5000000000000 : ℝ), (32790526092611/100000000000000 : ℝ), (16395263207673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224225207/500000000 : ℝ)|^8255 ≤ (1720947373889/5000000000000 : ℝ)^6207
        have hw : |(224225207/500000000 : ℝ)|=(224225207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2162008377/5000000000 : ℝ)|^8255 ≤ (32790526092611/100000000000000 : ℝ)^6207
        have hw : |(2162008377/5000000000 : ℝ)|=(2162008377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2162008393/5000000000 : ℝ)|^8255 ≤ (16395263207673/50000000000000 : ℝ)^6207
        have hw : |(2162008393/5000000000 : ℝ)|=(2162008393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2336732399/10000000000 : ℝ)*x 0 + (2640014379/5000000000 : ℝ)*x 1 + (5280028733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2336732399/10000000000 : ℝ)^8255 ≤ (3615942253569/25000000000000 : ℝ)^6207 := by
    have hnat : (2336732399 : ℕ)^8255*25000000000000^6207 ≤ 3615942253569^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336732399 10000000000 3615942253569 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640014379/5000000000 : ℝ)^8255 ≤ (1069202890571/2500000000000 : ℝ)^6207 := by
    have hnat : (2640014379 : ℕ)^8255*2500000000000^6207 ≤ 1069202890571^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640014379 5000000000 1069202890571 2500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280028733/10000000000 : ℝ)^8255 ≤ (21384057676763/50000000000000 : ℝ)^6207 := by
    have hnat : (5280028733 : ℕ)^8255*50000000000000^6207 ≤ 21384057676763^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280028733 10000000000 21384057676763 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2336732399/10000000000 : ℝ), (2640014379/5000000000 : ℝ), (5280028733/10000000000 : ℝ)] ![(3615942253569/25000000000000 : ℝ), (1069202890571/2500000000000 : ℝ), (21384057676763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2336732399/10000000000 : ℝ)|^8255 ≤ (3615942253569/25000000000000 : ℝ)^6207
        have hw : |(-2336732399/10000000000 : ℝ)|=(2336732399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640014379/5000000000 : ℝ)|^8255 ≤ (1069202890571/2500000000000 : ℝ)^6207
        have hw : |(2640014379/5000000000 : ℝ)|=(2640014379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280028733/10000000000 : ℝ)|^8255 ≤ (21384057676763/50000000000000 : ℝ)^6207
        have hw : |(5280028733/10000000000 : ℝ)|=(5280028733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67051127/125000000 : ℝ)*x 0 + (-556389631/2500000000 : ℝ)*x 1 + (5280028763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67051127/125000000 : ℝ)^8255 ≤ (21838021333041/50000000000000 : ℝ)^6207 := by
    have hnat : (67051127 : ℕ)^8255*50000000000000^6207 ≤ 21838021333041^6207*125000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67051127 125000000 21838021333041 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556389631/2500000000 : ℝ)^8255 ≤ (13555841637827/100000000000000 : ℝ)^6207 := by
    have hnat : (556389631 : ℕ)^8255*100000000000000^6207 ≤ 13555841637827^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556389631 2500000000 13555841637827 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280028763/10000000000 : ℝ)^8255 ≤ (42768115676703/100000000000000 : ℝ)^6207 := by
    have hnat : (5280028763 : ℕ)^8255*100000000000000^6207 ≤ 42768115676703^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280028763 10000000000 42768115676703 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67051127/125000000 : ℝ), (-556389631/2500000000 : ℝ), (5280028763/10000000000 : ℝ)] ![(21838021333041/50000000000000 : ℝ), (13555841637827/100000000000000 : ℝ), (42768115676703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67051127/125000000 : ℝ)|^8255 ≤ (21838021333041/50000000000000 : ℝ)^6207
        have hw : |(67051127/125000000 : ℝ)|=(67051127/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556389631/2500000000 : ℝ)|^8255 ≤ (13555841637827/100000000000000 : ℝ)^6207
        have hw : |(-556389631/2500000000 : ℝ)|=(556389631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280028763/10000000000 : ℝ)|^8255 ≤ (42768115676703/100000000000000 : ℝ)^6207
        have hw : |(5280028763/10000000000 : ℝ)|=(5280028763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682045099/5000000000 : ℝ)*x 0 + (2640014367/5000000000 : ℝ)*x 1 + (-2225558513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682045099/5000000000 : ℝ)^8255 ≤ (21838021538789/50000000000000 : ℝ)^6207 := by
    have hnat : (2682045099 : ℕ)^8255*50000000000000^6207 ≤ 21838021538789^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682045099 5000000000 21838021538789 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640014367/5000000000 : ℝ)^8255 ≤ (42768115364299/100000000000000 : ℝ)^6207 := by
    have hnat : (2640014367 : ℕ)^8255*100000000000000^6207 ≤ 42768115364299^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640014367 5000000000 42768115364299 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225558513/10000000000 : ℝ)^8255 ≤ (169448019359/1250000000000 : ℝ)^6207 := by
    have hnat : (2225558513 : ℕ)^8255*1250000000000^6207 ≤ 169448019359^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225558513 10000000000 169448019359 1250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682045099/5000000000 : ℝ), (2640014367/5000000000 : ℝ), (-2225558513/10000000000 : ℝ)] ![(21838021538789/50000000000000 : ℝ), (42768115364299/100000000000000 : ℝ), (169448019359/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682045099/5000000000 : ℝ)|^8255 ≤ (21838021538789/50000000000000 : ℝ)^6207
        have hw : |(2682045099/5000000000 : ℝ)|=(2682045099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640014367/5000000000 : ℝ)|^8255 ≤ (42768115364299/100000000000000 : ℝ)^6207
        have hw : |(2640014367/5000000000 : ℝ)|=(2640014367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225558513/10000000000 : ℝ)|^8255 ≤ (169448019359/1250000000000 : ℝ)^6207
        have hw : |(-2225558513/10000000000 : ℝ)|=(2225558513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4267306363/10000000000 : ℝ)*x 0 + (554074273/1250000000 : ℝ)*x 1 + (4432594139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267306363/10000000000 : ℝ)^8255 ≤ (251717312803/781250000000 : ℝ)^6207 := by
    have hnat : (4267306363 : ℕ)^8255*781250000000^6207 ≤ 251717312803^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267306363 10000000000 251717312803 781250000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554074273/1250000000 : ℝ)^8255 ≤ (8472523049053/25000000000000 : ℝ)^6207 := by
    have hnat : (554074273 : ℕ)^8255*25000000000000^6207 ≤ 8472523049053^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554074273 1250000000 8472523049053 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432594139/10000000000 : ℝ)^8255 ≤ (33890091738637/100000000000000 : ℝ)^6207 := by
    have hnat : (4432594139 : ℕ)^8255*100000000000000^6207 ≤ 33890091738637^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432594139 10000000000 33890091738637 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267306363/10000000000 : ℝ), (554074273/1250000000 : ℝ), (4432594139/10000000000 : ℝ)] ![(251717312803/781250000000 : ℝ), (8472523049053/25000000000000 : ℝ), (33890091738637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267306363/10000000000 : ℝ)|^8255 ≤ (251717312803/781250000000 : ℝ)^6207
        have hw : |(4267306363/10000000000 : ℝ)|=(4267306363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554074273/1250000000 : ℝ)|^8255 ≤ (8472523049053/25000000000000 : ℝ)^6207
        have hw : |(554074273/1250000000 : ℝ)|=(554074273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4432594139/10000000000 : ℝ)|^8255 ≤ (33890091738637/100000000000000 : ℝ)^6207
        have hw : |(4432594139/10000000000 : ℝ)|=(4432594139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_8 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2282336177/10000000000 : ℝ)*x 0 + (1303487293/2500000000 : ℝ)*x 1 + (2693511391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2282336177/10000000000 : ℝ)^8255 ≤ (14017705506821/100000000000000 : ℝ)^6207 := by
    have hnat : (2282336177 : ℕ)^8255*100000000000000^6207 ≤ 14017705506821^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282336177 10000000000 14017705506821 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303487293/2500000000 : ℝ)^8255 ≤ (42057742781139/100000000000000 : ℝ)^6207 := by
    have hnat : (1303487293 : ℕ)^8255*100000000000000^6207 ≤ 42057742781139^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303487293 2500000000 42057742781139 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693511391/5000000000 : ℝ)^8255 ≤ (10981137923/25000000000 : ℝ)^6207 := by
    have hnat : (2693511391 : ℕ)^8255*25000000000^6207 ≤ 10981137923^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693511391 5000000000 10981137923 25000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2282336177/10000000000 : ℝ), (1303487293/2500000000 : ℝ), (2693511391/5000000000 : ℝ)] ![(14017705506821/100000000000000 : ℝ), (42057742781139/100000000000000 : ℝ), (10981137923/25000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2282336177/10000000000 : ℝ)|^8255 ≤ (14017705506821/100000000000000 : ℝ)^6207
        have hw : |(-2282336177/10000000000 : ℝ)|=(2282336177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303487293/2500000000 : ℝ)|^8255 ≤ (42057742781139/100000000000000 : ℝ)^6207
        have hw : |(1303487293/2500000000 : ℝ)|=(1303487293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693511391/5000000000 : ℝ)|^8255 ≤ (10981137923/25000000000 : ℝ)^6207
        have hw : |(2693511391/5000000000 : ℝ)|=(2693511391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_9 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644178923/5000000000 : ℝ)*x 0 + (-2183671373/10000000000 : ℝ)*x 1 + (5387022731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644178923/5000000000 : ℝ)^8255 ≤ (4285786461453/10000000000000 : ℝ)^6207 := by
    have hnat : (2644178923 : ℕ)^8255*10000000000000^6207 ≤ 4285786461453^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644178923 5000000000 4285786461453 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183671373/10000000000 : ℝ)^8255 ≤ (13217584232291/100000000000000 : ℝ)^6207 := by
    have hnat : (2183671373 : ℕ)^8255*100000000000000^6207 ≤ 13217584232291^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183671373 10000000000 13217584232291 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387022731/10000000000 : ℝ)^8255 ≤ (43924551138951/100000000000000 : ℝ)^6207 := by
    have hnat : (5387022731 : ℕ)^8255*100000000000000^6207 ≤ 43924551138951^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387022731 10000000000 43924551138951 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644178923/5000000000 : ℝ), (-2183671373/10000000000 : ℝ), (5387022731/10000000000 : ℝ)] ![(4285786461453/10000000000000 : ℝ), (13217584232291/100000000000000 : ℝ), (43924551138951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644178923/5000000000 : ℝ)|^8255 ≤ (4285786461453/10000000000000 : ℝ)^6207
        have hw : |(2644178923/5000000000 : ℝ)|=(2644178923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183671373/10000000000 : ℝ)|^8255 ≤ (13217584232291/100000000000000 : ℝ)^6207
        have hw : |(-2183671373/10000000000 : ℝ)|=(2183671373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387022731/10000000000 : ℝ)|^8255 ≤ (43924551138951/100000000000000 : ℝ)^6207
        have hw : |(5387022731/10000000000 : ℝ)|=(5387022731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_10 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661044739/1250000000 : ℝ)*x 0 + (1077404549/2000000000 : ℝ)*x 1 + (-1091835633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661044739/1250000000 : ℝ)^8255 ≤ (42857865325889/100000000000000 : ℝ)^6207 := by
    have hnat : (661044739 : ℕ)^8255*100000000000000^6207 ≤ 42857865325889^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661044739 1250000000 42857865325889 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077404549/2000000000 : ℝ)^8255 ≤ (2745284455673/6250000000000 : ℝ)^6207 := by
    have hnat : (1077404549 : ℕ)^8255*6250000000000^6207 ≤ 2745284455673^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077404549 2000000000 2745284455673 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091835633/5000000000 : ℝ)^8255 ≤ (3304395842733/25000000000000 : ℝ)^6207 := by
    have hnat : (1091835633 : ℕ)^8255*25000000000000^6207 ≤ 3304395842733^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091835633 5000000000 3304395842733 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661044739/1250000000 : ℝ), (1077404549/2000000000 : ℝ), (-1091835633/5000000000 : ℝ)] ![(42857865325889/100000000000000 : ℝ), (2745284455673/6250000000000 : ℝ), (3304395842733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661044739/1250000000 : ℝ)|^8255 ≤ (42857865325889/100000000000000 : ℝ)^6207
        have hw : |(661044739/1250000000 : ℝ)|=(661044739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077404549/2000000000 : ℝ)|^8255 ≤ (2745284455673/6250000000000 : ℝ)^6207
        have hw : |(1077404549/2000000000 : ℝ)|=(1077404549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091835633/5000000000 : ℝ)|^8255 ≤ (3304395842733/25000000000000 : ℝ)^6207
        have hw : |(-1091835633/5000000000 : ℝ)|=(1091835633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_11 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4505640939/10000000000 : ℝ)*x 0 + (2156653887/5000000000 : ℝ)*x 1 + (2156653951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505640939/10000000000 : ℝ)^8255 ≤ (17317434247453/50000000000000 : ℝ)^6207 := by
    have hnat : (4505640939 : ℕ)^8255*50000000000000^6207 ≤ 17317434247453^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505640939 10000000000 17317434247453 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156653887/5000000000 : ℝ)^8255 ≤ (4085320637251/12500000000000 : ℝ)^6207 := by
    have hnat : (2156653887 : ℕ)^8255*12500000000000^6207 ≤ 4085320637251^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156653887 5000000000 4085320637251 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156653951/5000000000 : ℝ)^8255 ≤ (32682566387893/100000000000000 : ℝ)^6207 := by
    have hnat : (2156653951 : ℕ)^8255*100000000000000^6207 ≤ 32682566387893^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156653951 5000000000 32682566387893 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505640939/10000000000 : ℝ), (2156653887/5000000000 : ℝ), (2156653951/5000000000 : ℝ)] ![(17317434247453/50000000000000 : ℝ), (4085320637251/12500000000000 : ℝ), (32682566387893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505640939/10000000000 : ℝ)|^8255 ≤ (17317434247453/50000000000000 : ℝ)^6207
        have hw : |(4505640939/10000000000 : ℝ)|=(4505640939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156653887/5000000000 : ℝ)|^8255 ≤ (4085320637251/12500000000000 : ℝ)^6207
        have hw : |(2156653887/5000000000 : ℝ)|=(2156653887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156653951/5000000000 : ℝ)|^8255 ≤ (32682566387893/100000000000000 : ℝ)^6207
        have hw : |(2156653951/5000000000 : ℝ)|=(2156653951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_12 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266363311/1250000000 : ℝ)*x 0 + (680270417/1250000000 : ℝ)*x 1 + (5272029579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266363311/1250000000 : ℝ)^8255 ≤ (6397262612629/50000000000000 : ℝ)^6207 := by
    have hnat : (266363311 : ℕ)^8255*50000000000000^6207 ≤ 6397262612629^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266363311 1250000000 6397262612629 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680270417/1250000000 : ℝ)^8255 ≤ (44523509279003/100000000000000 : ℝ)^6207 := by
    have hnat : (680270417 : ℕ)^8255*100000000000000^6207 ≤ 44523509279003^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680270417 1250000000 44523509279003 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272029579/10000000000 : ℝ)^8255 ≤ (42681965484489/100000000000000 : ℝ)^6207 := by
    have hnat : (5272029579 : ℕ)^8255*100000000000000^6207 ≤ 42681965484489^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272029579 10000000000 42681965484489 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266363311/1250000000 : ℝ), (680270417/1250000000 : ℝ), (5272029579/10000000000 : ℝ)] ![(6397262612629/50000000000000 : ℝ), (44523509279003/100000000000000 : ℝ), (42681965484489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266363311/1250000000 : ℝ)|^8255 ≤ (6397262612629/50000000000000 : ℝ)^6207
        have hw : |(-266363311/1250000000 : ℝ)|=(266363311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680270417/1250000000 : ℝ)|^8255 ≤ (44523509279003/100000000000000 : ℝ)^6207
        have hw : |(680270417/1250000000 : ℝ)|=(680270417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272029579/10000000000 : ℝ)|^8255 ≤ (42681965484489/100000000000000 : ℝ)^6207
        have hw : |(5272029579/10000000000 : ℝ)|=(5272029579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_13 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369749547/10000000000 : ℝ)*x 0 + (-2228625411/10000000000 : ℝ)*x 1 + (5272030067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369749547/10000000000 : ℝ)^8255 ≤ (21868669006357/50000000000000 : ℝ)^6207 := by
    have hnat : (5369749547 : ℕ)^8255*50000000000000^6207 ≤ 21868669006357^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369749547 10000000000 21868669006357 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228625411/10000000000 : ℝ)^8255 ≤ (13580691230001/100000000000000 : ℝ)^6207 := by
    have hnat : (2228625411 : ℕ)^8255*100000000000000^6207 ≤ 13580691230001^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228625411 10000000000 13580691230001 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272030067/10000000000 : ℝ)^8255 ≤ (5335246342359/12500000000000 : ℝ)^6207 := by
    have hnat : (5272030067 : ℕ)^8255*12500000000000^6207 ≤ 5335246342359^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272030067 10000000000 5335246342359 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369749547/10000000000 : ℝ), (-2228625411/10000000000 : ℝ), (5272030067/10000000000 : ℝ)] ![(21868669006357/50000000000000 : ℝ), (13580691230001/100000000000000 : ℝ), (5335246342359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369749547/10000000000 : ℝ)|^8255 ≤ (21868669006357/50000000000000 : ℝ)^6207
        have hw : |(5369749547/10000000000 : ℝ)|=(5369749547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228625411/10000000000 : ℝ)|^8255 ≤ (13580691230001/100000000000000 : ℝ)^6207
        have hw : |(-2228625411/10000000000 : ℝ)|=(2228625411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272030067/10000000000 : ℝ)|^8255 ≤ (5335246342359/12500000000000 : ℝ)^6207
        have hw : |(5272030067/10000000000 : ℝ)|=(5272030067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_14 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268487483/500000000 : ℝ)*x 0 + (1054405853/2000000000 : ℝ)*x 1 + (-89145053/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268487483/500000000 : ℝ)^8255 ≤ (43737339236801/100000000000000 : ℝ)^6207 := by
    have hnat : (268487483 : ℕ)^8255*100000000000000^6207 ≤ 43737339236801^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268487483 500000000 43737339236801 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054405853/2000000000 : ℝ)^8255 ≤ (8536392420719/20000000000000 : ℝ)^6207 := by
    have hnat : (1054405853 : ℕ)^8255*20000000000000^6207 ≤ 8536392420719^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054405853 2000000000 8536392420719 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89145053/400000000 : ℝ)^8255 ≤ (1358069863741/10000000000000 : ℝ)^6207 := by
    have hnat : (89145053 : ℕ)^8255*10000000000000^6207 ≤ 1358069863741^6207*400000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89145053 400000000 1358069863741 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268487483/500000000 : ℝ), (1054405853/2000000000 : ℝ), (-89145053/400000000 : ℝ)] ![(43737339236801/100000000000000 : ℝ), (8536392420719/20000000000000 : ℝ), (1358069863741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268487483/500000000 : ℝ)|^8255 ≤ (43737339236801/100000000000000 : ℝ)^6207
        have hw : |(268487483/500000000 : ℝ)|=(268487483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054405853/2000000000 : ℝ)|^8255 ≤ (8536392420719/20000000000000 : ℝ)^6207
        have hw : |(1054405853/2000000000 : ℝ)|=(1054405853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89145053/400000000 : ℝ)|^8255 ≤ (1358069863741/10000000000000 : ℝ)^6207
        have hw : |(-89145053/400000000 : ℝ)|=(89145053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_box_15 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (3319717/7812500 : ℝ)*x 0 + (4441506857/10000000000 : ℝ)*x 1 + (4441506539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3319717/7812500 : ℝ)^8255 ≤ (32038504527849/100000000000000 : ℝ)^6207 := by
    have hnat : (3319717 : ℕ)^8255*100000000000000^6207 ≤ 32038504527849^6207*7812500^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319717 7812500 32038504527849 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4441506857/10000000000 : ℝ)^8255 ≤ (339807493453/1000000000000 : ℝ)^6207 := by
    have hnat : (4441506857 : ℕ)^8255*1000000000000^6207 ≤ 339807493453^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441506857 10000000000 339807493453 1000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4441506539/10000000000 : ℝ)^8255 ≤ (4247593263703/12500000000000 : ℝ)^6207 := by
    have hnat : (4441506539 : ℕ)^8255*12500000000000^6207 ≤ 4247593263703^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441506539 10000000000 4247593263703 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3319717/7812500 : ℝ), (4441506857/10000000000 : ℝ), (4441506539/10000000000 : ℝ)] ![(32038504527849/100000000000000 : ℝ), (339807493453/1000000000000 : ℝ), (4247593263703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3319717/7812500 : ℝ)|^8255 ≤ (32038504527849/100000000000000 : ℝ)^6207
        have hw : |(3319717/7812500 : ℝ)|=(3319717/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4441506857/10000000000 : ℝ)|^8255 ≤ (339807493453/1000000000000 : ℝ)^6207
        have hw : |(4441506857/10000000000 : ℝ)|=(4441506857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4441506539/10000000000 : ℝ)|^8255 ≤ (4247593263703/12500000000000 : ℝ)^6207
        have hw : |(4441506539/10000000000 : ℝ)|=(4441506539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29619/50000 : ℝ) ∧ (1989/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82943/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (4127/1024 : ℝ) ≤ (14971412152731009/100000000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^4127 ≤ (14971412152731009/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5623 : ℕ)^4127*100000000000000000000^1024 ≤ 14971412152731009^1024*50000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 14971412152731009 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (14971412152731009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7/50 : ℝ) ^ (4127/1024 : ℝ) ≤ (18098080161914269/50000000000000000000 : ℝ) := by
    have hpowers : (7/50 : ℝ)^4127 ≤ (18098080161914269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7 : ℕ)^4127*50000000000000000000^1024 ≤ 18098080161914269^1024*50^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 50 18098080161914269 50000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/50 : ℝ)) (X := (18098080161914269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014971412152731009/50000000000000000000 : ℝ) ≤ (5000371432047887/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50014971412152731009/50000000000000000000 : ℝ)^1024 ≤ (5000371432047887/5000000000000000 : ℝ)^4127 := by
      have hnat : (50014971412152731009 : ℕ)^1024*5000000000000000^4127 ≤ 5000371432047887^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014971412152731009 50000000000000000000 5000371432047887 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000371432047887/5000000000000000 : ℝ)) (X := (50014971412152731009/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051167572476559547/100000000000000000000 : ℝ) ≤ (10001269336527049/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (100051167572476559547/100000000000000000000 : ℝ)^1024 ≤ (10001269336527049/10000000000000000 : ℝ)^4127 := by
      have hnat : (100051167572476559547 : ℕ)^1024*10000000000000000^4127 ≤ 10001269336527049^4127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051167572476559547 100000000000000000000 10001269336527049 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001269336527049/10000000000000000 : ℝ)) (X := (100051167572476559547/100000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018098080161914269/25000000000000000000 : ℝ) ≤ (2500448952239581/2500000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (25018098080161914269/25000000000000000000 : ℝ)^1024 ≤ (2500448952239581/2500000000000000 : ℝ)^4127 := by
      have hnat : (25018098080161914269 : ℕ)^1024*2500000000000000^4127 ≤ 2500448952239581^4127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018098080161914269 25000000000000000000 2500448952239581 2500000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500448952239581/2500000000000000 : ℝ)) (X := (25018098080161914269/25000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14971412152731009/100000000000000000000 : ℝ) ≤ ((1147091851241480179/1147500000000000000 : ℝ)+2*(7019632417/3672000000000 : ℝ)*(5623/50000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1147091851241480179/1147500000000000000 : ℝ)+2*(7019632417/3672000000000 : ℝ)*(5623/50000 : ℝ)=(5000371432047887/5000000000000000 : ℝ) by norm_num, show 1+2*(14971412152731009/100000000000000000000 : ℝ)=(50014971412152731009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18098080161914269/50000000000000000000 : ℝ)+(14971412152731009/100000000000000000000 : ℝ) ≤ ((1147091851241480179/1147500000000000000 : ℝ)+(7019632417/3672000000000 : ℝ)*((7/50 : ℝ)+(5623/50000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (1147091851241480179/1147500000000000000 : ℝ)+(7019632417/3672000000000 : ℝ)*((7/50 : ℝ)+(5623/50000 : ℝ))=(10001269336527049/10000000000000000 : ℝ) by norm_num, show 1+(18098080161914269/50000000000000000000 : ℝ)+(14971412152731009/100000000000000000000 : ℝ)=(100051167572476559547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18098080161914269/50000000000000000000 : ℝ) ≤ ((1147091851241480179/1147500000000000000 : ℝ)+2*(7019632417/3672000000000 : ℝ)*(7/50 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1147091851241480179/1147500000000000000 : ℝ)+2*(7019632417/3672000000000 : ℝ)*(7/50 : ℝ)=(2500448952239581/2500000000000000 : ℝ) by norm_num, show 1+2*(18098080161914269/50000000000000000000 : ℝ)=(25018098080161914269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1147091851241480179/1147500000000000000 : ℝ)*(X 1 0+X 2 0)+(7019632417/3672000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (1147091851241480179/1147500000000000000 : ℝ)) (alpha := (7019632417/3672000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1147091851241480179/1147500000000000000 : ℝ)*(X 0 1+X 2 1)+(7019632417/3672000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (1147091851241480179/1147500000000000000 : ℝ)) (alpha := (7019632417/3672000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1147091851241480179/1147500000000000000 : ℝ)*(X 0 2+X 1 2)+(7019632417/3672000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (1147091851241480179/1147500000000000000 : ℝ)) (alpha := (7019632417/3672000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2076139017/10000000000 : ℝ)*X 0 0+(5377421597/10000000000 : ℝ)*X 0 1+(5377423089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295156443/10000000000 : ℝ)*X 1 0+(-2187494431/10000000000 : ℝ)*X 1 1+(2688711183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295156721/10000000000 : ℝ)*X 2 0+(5377422761/10000000000 : ℝ)*X 2 1+(-273436691/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((224225207/500000000 : ℝ)*X 0 0+(2162008377/5000000000 : ℝ)*X 0 1+(2162008393/5000000000 : ℝ)*X 0 2+(224225207/500000000 : ℝ)*X 1 0+(2162008377/5000000000 : ℝ)*X 1 1+(2162008393/5000000000 : ℝ)*X 1 2+(224225207/500000000 : ℝ)*X 2 0+(2162008377/5000000000 : ℝ)*X 2 1+(2162008393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2336732399/10000000000 : ℝ)*X 0 0+(2640014379/5000000000 : ℝ)*X 0 1+(5280028733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((67051127/125000000 : ℝ)*X 1 0+(-556389631/2500000000 : ℝ)*X 1 1+(5280028763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682045099/5000000000 : ℝ)*X 2 0+(2640014367/5000000000 : ℝ)*X 2 1+(-2225558513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267306363/10000000000 : ℝ)*X 0 0+(554074273/1250000000 : ℝ)*X 0 1+(4432594139/10000000000 : ℝ)*X 0 2+(4267306363/10000000000 : ℝ)*X 1 0+(554074273/1250000000 : ℝ)*X 1 1+(4432594139/10000000000 : ℝ)*X 1 2+(4267306363/10000000000 : ℝ)*X 2 0+(554074273/1250000000 : ℝ)*X 2 1+(4432594139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2282336177/10000000000 : ℝ)*X 0 0+(1303487293/2500000000 : ℝ)*X 0 1+(2693511391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644178923/5000000000 : ℝ)*X 1 0+(-2183671373/10000000000 : ℝ)*X 1 1+(5387022731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((661044739/1250000000 : ℝ)*X 2 0+(1077404549/2000000000 : ℝ)*X 2 1+(-1091835633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4505640939/10000000000 : ℝ)*X 0 0+(2156653887/5000000000 : ℝ)*X 0 1+(2156653951/5000000000 : ℝ)*X 0 2+(4505640939/10000000000 : ℝ)*X 1 0+(2156653887/5000000000 : ℝ)*X 1 1+(2156653951/5000000000 : ℝ)*X 1 2+(4505640939/10000000000 : ℝ)*X 2 0+(2156653887/5000000000 : ℝ)*X 2 1+(2156653951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-266363311/1250000000 : ℝ)*X 0 0+(680270417/1250000000 : ℝ)*X 0 1+(5272029579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369749547/10000000000 : ℝ)*X 1 0+(-2228625411/10000000000 : ℝ)*X 1 1+(5272030067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268487483/500000000 : ℝ)*X 2 0+(1054405853/2000000000 : ℝ)*X 2 1+(-89145053/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3319717/7812500 : ℝ)*X 0 0+(4441506857/10000000000 : ℝ)*X 0 1+(4441506539/10000000000 : ℝ)*X 0 2+(3319717/7812500 : ℝ)*X 1 0+(4441506857/10000000000 : ℝ)*X 1 1+(4441506539/10000000000 : ℝ)*X 1 2+(3319717/7812500 : ℝ)*X 2 0+(4441506857/10000000000 : ℝ)*X 2 1+(4441506539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-2379986708216186016091860891733/3825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (838153/1562500000000 : ℝ)*(upper0) + (41356771/50000000000000 : ℝ)*(upper1) + (31776711/100000000000000 : ℝ)*(upper3) + (65308067/100000000000000 : ℝ)*(upper5) + (770622993871127/20000000000000 : ℝ)*(major0) + (770622993871127/20000000000000 : ℝ)*(major1) + (963278742338909/25000000000000 : ℝ)*(major2) + (41556131/625000000000 : ℝ)*(sp3) + (5122018858231147/100000000000000 : ℝ)*(sp4) + (5121988092168017/100000000000000 : ℝ)*(sp5) + (5122022484029439/100000000000000 : ℝ)*(sp6) + (81404419706533/3125000000000 : ℝ)*(sp7) + (3625798293/100000000000000 : ℝ)*(sp8) + (17195930711/50000000000000 : ℝ)*(sp13) + (20351156871797/781250000000 : ℝ)*(f.failure) + (5122022484029439/100000000000000 : ℝ)*(f.sum) + (45556609153/68000000000000000000000000 : ℝ)*base65 + (494339331155558267/22950000000000000000000000000000 : ℝ)*base68 + (1006958992384015793/14343750000000000000000000000000 : ℝ)*base69 + (111653965742241733/22950000000000000000000000000000 : ℝ)*base71 + (555916486287/68000000000000000000000000 : ℝ)*base74 + (350344031956984207/14343750000000000000000000000000 : ℝ)*base76 + (9920340307842137/2550000000000000000000000000000 : ℝ)*base77 + (59202921121842137/2550000000000000000000000000000 : ℝ)*base79 + (3112387719209/918000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (796357/78125000000000000000 : ℝ)*base89 + (796357/78125000000000000000 : ℝ)*base91 + (15107/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29619/50000 : ℝ) ≤ (377656521418183547235467202991/637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85481947/25000000000000 : ℝ)*(lower3) + (345551089/100000000000000 : ℝ)*(upper4) + (10694919/50000000000000 : ℝ)*(upper5) + (489495225850391/12500000000000 : ℝ)*(major0) + (489495225850391/12500000000000 : ℝ)*(major1) + (391596180680313/10000000000000 : ℝ)*(major2) + (206588848671451/4000000000000 : ℝ)*(sp0) + (2582361437936593/50000000000000 : ℝ)*(sp1) + (80698337130637/1562500000000 : ℝ)*(sp2) + (82731927763453/3125000000000 : ℝ)*(sp3) + (17496754729/100000000000000 : ℝ)*(sp5) + (11699066787/25000000000000 : ℝ)*(sp6) + (1480632989/10000000000000 : ℝ)*(sp7) + (19155841641/100000000000000 : ℝ)*(sp12) + (2647436494760387/100000000000000 : ℝ)*(f.failure) + (1291185093156979/25000000000000 : ℝ)*(f.sum) + (3276111509179/918000000000000000000000000 : ℝ)*base65 + (2093657299713373/210937500000000000000000000000 : ℝ)*base67 + (20141626596266027/11475000000000000000000000000000 : ℝ)*base69 + (1173198851057629/421875000000000000000000000000 : ℝ)*base72 + (15702051593689/918000000000000000000000000 : ℝ)*base73 + (147546879814991027/11475000000000000000000000000000 : ℝ)*base75 + (12638568316802779/1593750000000000000000000000000 : ℝ)*base78 + (3357772483759721/1593750000000000000000000000000 : ℝ)*base79 + (658141858799/229500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (132754397/10000000000000000000000 : ℝ)*base89 + (132754397/10000000000000000000000 : ℝ)*base91 + (67245603/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1989/2500 : ℝ) ≤ (48692000920978464815924831/61200000000000000000000000 : ℝ) := by norm_num
    linear_combination (9162099/25000000000000 : ℝ)*(upper0) + (27508507/50000000000000 : ℝ)*(lower3) + (52541859/100000000000000 : ℝ)*(upper4) + (274012804444123/6250000000000 : ℝ)*(major0) + (274012804444123/6250000000000 : ℝ)*(major1) + (4384204871105969/100000000000000 : ℝ)*(major2) + (16857623729/50000000000000 : ℝ)*(sp1) + (54905819187/100000000000000 : ℝ)*(sp2) + (3757881121/12500000000000 : ℝ)*(sp3) + (31862041/5000000000000 : ℝ)*(sp4) + (5777890148659947/100000000000000 : ℝ)*(sp8) + (5777857070653309/100000000000000 : ℝ)*(sp9) + (5777835880081579/100000000000000 : ℝ)*(sp10) + (1481984097796407/50000000000000 : ℝ)*(sp11) + (1481999129320891/50000000000000 : ℝ)*(f.failure) + (5777890785900767/100000000000000 : ℝ)*(f.sum) + (440813775211/612000000000000000000000000 : ℝ)*base65 + (157070920130980193/28687500000000000000000000000000 : ℝ)*base67 + (365460414099588451/114750000000000000000000000000000 : ℝ)*base69 + (282139375825144807/28687500000000000000000000000000 : ℝ)*base72 + (17146451589379/612000000000000000000000000 : ℝ)*base73 + (67929553872161549/114750000000000000000000000000000 : ℝ)*base76 + (90324960680993/23437500000000000000000000000 : ℝ)*base78 + (1047422258528639/46875000000000000000000000000 : ℝ)*base79 + (5541953059/13500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (65390821/5000000000000000000000 : ℝ)*base89 + (65390821/5000000000000000000000 : ℝ)*base91 + (15390821/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82943/100000 : ℝ) ≤ (-17624939470990036245530491121/21250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44757213/20000000000000 : ℝ)*(lower0) + (19071313/12500000000000 : ℝ)*(upper3) + (6337203/1562500000000 : ℝ)*(lower4) + (44187197284791/1000000000000 : ℝ)*(major0) + (44187197284791/1000000000000 : ℝ)*(major1) + (44187197284791/1000000000000 : ℝ)*(major2) + (3663359659/20000000000000 : ℝ)*(sp0) + (14698215551/20000000000000 : ℝ)*(sp5) + (907490953267/100000000000000 : ℝ)*(sp6) + (7370761721/4000000000000 : ℝ)*(sp7) + (5877735630831017/100000000000000 : ℝ)*(sp12) + (2938840228275779/50000000000000 : ℝ)*(sp13) + (2938423228338023/50000000000000 : ℝ)*(sp14) + (746787051040479/25000000000000 : ℝ)*(sp15) + (149366623660247/5000000000000 : ℝ)*(f.failure) + (5877753947629313/100000000000000 : ℝ)*(f.sum) + (52718251187/25500000000000000000000000 : ℝ)*base66 + (35179783218793/42500000000000000000000000000 : ℝ)*base68 + (352356897816207/42500000000000000000000000000 : ℝ)*base69 + (156127301846207/42500000000000000000000000000 : ℝ)*base71 + (372351396901/12750000000000000000000000 : ℝ)*base74 + (375144347186293/42500000000000000000000000000 : ℝ)*base76 + (122705888346207/42500000000000000000000000000 : ℝ)*base77 + (704622377288707/42500000000000000000000000000 : ℝ)*base79 + (58885151393/12750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (522057/500000000000000000000 : ℝ)*base89 + (522057/500000000000000000000 : ℝ)*base91 + (522057/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1062_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (1989/2500 : ℝ) ≤ X j i ∧ X j i ≤ (82943/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1062_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1062_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (1989/2500 : ℝ) ≤ X j i ∧ X j i ≤ (82943/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1062_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (1989/2500 : ℝ) ≤ X j i ∧ X j i ≤ (82943/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
