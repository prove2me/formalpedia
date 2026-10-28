-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:55.328745+00:00
-- url     : https://prove2.me/submissions/74f9e31e-17af-4eae-b12e-047b98ee9ef8

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
theorem support_rectangle_w1079_s6_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098669851/5000000000 : ℝ)*x 0 + (1348662557/2500000000 : ℝ)*x 1 + (5264196861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098669851/5000000000 : ℝ)^517 ≤ (13345942167189/100000000000000 : ℝ)^389 := by
    have hnat : (1098669851 : ℕ)^517*100000000000000^389 ≤ 13345942167189^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098669851 5000000000 13345942167189 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348662557/2500000000 : ℝ)^517 ≤ (22015883943333/50000000000000 : ℝ)^389 := by
    have hnat : (1348662557 : ℕ)^517*50000000000000^389 ≤ 22015883943333^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348662557 2500000000 22015883943333 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264196861/10000000000 : ℝ)^517 ≤ (42622289928663/100000000000000 : ℝ)^389 := by
    have hnat : (5264196861 : ℕ)^517*100000000000000^389 ≤ 42622289928663^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264196861 10000000000 42622289928663 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098669851/5000000000 : ℝ), (1348662557/2500000000 : ℝ), (5264196861/10000000000 : ℝ)] ![(13345942167189/100000000000000 : ℝ), (22015883943333/50000000000000 : ℝ), (42622289928663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098669851/5000000000 : ℝ)|^517 ≤ (13345942167189/100000000000000 : ℝ)^389
        have hw : |(-1098669851/5000000000 : ℝ)|=(1098669851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348662557/2500000000 : ℝ)|^517 ≤ (22015883943333/50000000000000 : ℝ)^389
        have hw : |(1348662557/2500000000 : ℝ)|=(1348662557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264196861/10000000000 : ℝ)|^517 ≤ (42622289928663/100000000000000 : ℝ)^389
        have hw : |(5264196861/10000000000 : ℝ)|=(5264196861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1069015463/2000000000 : ℝ)*x 0 + (-1131765667/5000000000 : ℝ)*x 1 + (2632098481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069015463/2000000000 : ℝ)^517 ≤ (8698964586211/20000000000000 : ℝ)^389 := by
    have hnat : (1069015463 : ℕ)^517*20000000000000^389 ≤ 8698964586211^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069015463 2000000000 8698964586211 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131765667/5000000000 : ℝ)^517 ≤ (2776577207191/20000000000000 : ℝ)^389 := by
    have hnat : (1131765667 : ℕ)^517*20000000000000^389 ≤ 2776577207191^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131765667 5000000000 2776577207191 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632098481/5000000000 : ℝ)^517 ≤ (21311145507753/50000000000000 : ℝ)^389 := by
    have hnat : (2632098481 : ℕ)^517*50000000000000^389 ≤ 21311145507753^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632098481 5000000000 21311145507753 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069015463/2000000000 : ℝ), (-1131765667/5000000000 : ℝ), (2632098481/5000000000 : ℝ)] ![(8698964586211/20000000000000 : ℝ), (2776577207191/20000000000000 : ℝ), (21311145507753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069015463/2000000000 : ℝ)|^517 ≤ (8698964586211/20000000000000 : ℝ)^389
        have hw : |(1069015463/2000000000 : ℝ)|=(1069015463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1131765667/5000000000 : ℝ)|^517 ≤ (2776577207191/20000000000000 : ℝ)^389
        have hw : |(-1131765667/5000000000 : ℝ)|=(1131765667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632098481/5000000000 : ℝ)|^517 ≤ (21311145507753/50000000000000 : ℝ)^389
        have hw : |(2632098481/5000000000 : ℝ)|=(2632098481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345077067/10000000000 : ℝ)*x 0 + (5264197089/10000000000 : ℝ)*x 1 + (-282941437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345077067/10000000000 : ℝ)^517 ≤ (43494820248947/100000000000000 : ℝ)^389 := by
    have hnat : (5345077067 : ℕ)^517*100000000000000^389 ≤ 43494820248947^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345077067 10000000000 43494820248947 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264197089/10000000000 : ℝ)^517 ≤ (42622292382131/100000000000000 : ℝ)^389 := by
    have hnat : (5264197089 : ℕ)^517*100000000000000^389 ≤ 42622292382131^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264197089 10000000000 42622292382131 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282941437/1250000000 : ℝ)^517 ≤ (13882887356487/100000000000000 : ℝ)^389 := by
    have hnat : (282941437 : ℕ)^517*100000000000000^389 ≤ 13882887356487^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282941437 1250000000 13882887356487 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345077067/10000000000 : ℝ), (5264197089/10000000000 : ℝ), (-282941437/1250000000 : ℝ)] ![(43494820248947/100000000000000 : ℝ), (42622292382131/100000000000000 : ℝ), (13882887356487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345077067/10000000000 : ℝ)|^517 ≤ (43494820248947/100000000000000 : ℝ)^389
        have hw : |(5345077067/10000000000 : ℝ)|=(5345077067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264197089/10000000000 : ℝ)|^517 ≤ (42622292382131/100000000000000 : ℝ)^389
        have hw : |(5264197089/10000000000 : ℝ)|=(5264197089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282941437/1250000000 : ℝ)|^517 ≤ (13882887356487/100000000000000 : ℝ)^389
        have hw : |(-282941437/1250000000 : ℝ)|=(282941437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (874720007/2000000000 : ℝ)*x 0 + (4247331367/10000000000 : ℝ)*x 1 + (450366177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874720007/2000000000 : ℝ)^517 ≤ (16658181064787/50000000000000 : ℝ)^389 := by
    have hnat : (874720007 : ℕ)^517*50000000000000^389 ≤ 16658181064787^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874720007 2000000000 16658181064787 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247331367/10000000000 : ℝ)^517 ≤ (200275677709/625000000000 : ℝ)^389 := by
    have hnat : (4247331367 : ℕ)^517*625000000000^389 ≤ 200275677709^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247331367 10000000000 200275677709 625000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450366177/1000000000 : ℝ)^517 ≤ (8659882355281/25000000000000 : ℝ)^389 := by
    have hnat : (450366177 : ℕ)^517*25000000000000^389 ≤ 8659882355281^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450366177 1000000000 8659882355281 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874720007/2000000000 : ℝ), (4247331367/10000000000 : ℝ), (450366177/1000000000 : ℝ)] ![(16658181064787/50000000000000 : ℝ), (200275677709/625000000000 : ℝ), (8659882355281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874720007/2000000000 : ℝ)|^517 ≤ (16658181064787/50000000000000 : ℝ)^389
        have hw : |(874720007/2000000000 : ℝ)|=(874720007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247331367/10000000000 : ℝ)|^517 ≤ (200275677709/625000000000 : ℝ)^389
        have hw : |(4247331367/10000000000 : ℝ)|=(4247331367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450366177/1000000000 : ℝ)|^517 ≤ (8659882355281/25000000000000 : ℝ)^389
        have hw : |(450366177/1000000000 : ℝ)|=(450366177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-549336061/2500000000 : ℝ)*x 0 + (5264526623/10000000000 : ℝ)*x 1 + (215772789/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549336061/2500000000 : ℝ)^517 ≤ (1668247353903/12500000000000 : ℝ)^389 := by
    have hnat : (549336061 : ℕ)^517*12500000000000^389 ≤ 1668247353903^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549336061 2500000000 1668247353903 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264526623/10000000000 : ℝ)^517 ≤ (21312919238327/50000000000000 : ℝ)^389 := by
    have hnat : (5264526623 : ℕ)^517*50000000000000^389 ≤ 21312919238327^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264526623 10000000000 21312919238327 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215772789/400000000 : ℝ)^517 ≤ (44028182674997/100000000000000 : ℝ)^389 := by
    have hnat : (215772789 : ℕ)^517*100000000000000^389 ≤ 44028182674997^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215772789 400000000 44028182674997 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549336061/2500000000 : ℝ), (5264526623/10000000000 : ℝ), (215772789/400000000 : ℝ)] ![(1668247353903/12500000000000 : ℝ), (21312919238327/50000000000000 : ℝ), (44028182674997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549336061/2500000000 : ℝ)|^517 ≤ (1668247353903/12500000000000 : ℝ)^389
        have hw : |(-549336061/2500000000 : ℝ)|=(549336061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264526623/10000000000 : ℝ)|^517 ≤ (21312919238327/50000000000000 : ℝ)^389
        have hw : |(5264526623/10000000000 : ℝ)|=(5264526623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215772789/400000000 : ℝ)|^517 ≤ (44028182674997/100000000000000 : ℝ)^389
        have hw : |(215772789/400000000 : ℝ)|=(215772789/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328046143/2500000000 : ℝ)*x 0 + (-533352279/2500000000 : ℝ)*x 1 + (5394319737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328046143/2500000000 : ℝ)^517 ≤ (43139450220581/100000000000000 : ℝ)^389 := by
    have hnat : (1328046143 : ℕ)^517*100000000000000^389 ≤ 43139450220581^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328046143 2500000000 43139450220581 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533352279/2500000000 : ℝ)^517 ≤ (12832366963871/100000000000000 : ℝ)^389 := by
    have hnat : (533352279 : ℕ)^517*100000000000000^389 ≤ 12832366963871^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533352279 2500000000 12832366963871 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394319737/10000000000 : ℝ)^517 ≤ (44028182805169/100000000000000 : ℝ)^389 := by
    have hnat : (5394319737 : ℕ)^517*100000000000000^389 ≤ 44028182805169^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394319737 10000000000 44028182805169 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328046143/2500000000 : ℝ), (-533352279/2500000000 : ℝ), (5394319737/10000000000 : ℝ)] ![(43139450220581/100000000000000 : ℝ), (12832366963871/100000000000000 : ℝ), (44028182805169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328046143/2500000000 : ℝ)|^517 ≤ (43139450220581/100000000000000 : ℝ)^389
        have hw : |(1328046143/2500000000 : ℝ)|=(1328046143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533352279/2500000000 : ℝ)|^517 ≤ (12832366963871/100000000000000 : ℝ)^389
        have hw : |(-533352279/2500000000 : ℝ)|=(533352279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394319737/10000000000 : ℝ)|^517 ≤ (44028182805169/100000000000000 : ℝ)^389
        have hw : |(5394319737/10000000000 : ℝ)|=(5394319737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656092389/5000000000 : ℝ)*x 0 + (5394319673/10000000000 : ℝ)*x 1 + (-533352231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656092389/5000000000 : ℝ)^517 ≤ (43139452443941/100000000000000 : ℝ)^389 := by
    have hnat : (2656092389 : ℕ)^517*100000000000000^389 ≤ 43139452443941^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656092389 5000000000 43139452443941 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394319673/10000000000 : ℝ)^517 ≤ (1100704552773/2500000000000 : ℝ)^389 := by
    have hnat : (5394319673 : ℕ)^517*2500000000000^389 ≤ 1100704552773^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394319673 10000000000 1100704552773 2500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533352231/2500000000 : ℝ)^517 ≤ (1283236542899/10000000000000 : ℝ)^389 := by
    have hnat : (533352231 : ℕ)^517*10000000000000^389 ≤ 1283236542899^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533352231 2500000000 1283236542899 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656092389/5000000000 : ℝ), (5394319673/10000000000 : ℝ), (-533352231/2500000000 : ℝ)] ![(43139452443941/100000000000000 : ℝ), (1100704552773/2500000000000 : ℝ), (1283236542899/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656092389/5000000000 : ℝ)|^517 ≤ (43139452443941/100000000000000 : ℝ)^389
        have hw : |(2656092389/5000000000 : ℝ)|=(2656092389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394319673/10000000000 : ℝ)|^517 ≤ (1100704552773/2500000000000 : ℝ)^389
        have hw : |(5394319673/10000000000 : ℝ)|=(5394319673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533352231/2500000000 : ℝ)|^517 ≤ (1283236542899/10000000000000 : ℝ)^389
        have hw : |(-533352231/2500000000 : ℝ)|=(533352231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s6_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2186804901/5000000000 : ℝ)*x 0 + (900602939/2000000000 : ℝ)*x 1 + (2123990573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186804901/5000000000 : ℝ)^517 ≤ (1041139406637/3125000000000 : ℝ)^389 := by
    have hnat : (2186804901 : ℕ)^517*3125000000000^389 ≤ 1041139406637^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186804901 5000000000 1041139406637 3125000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900602939/2000000000 : ℝ)^517 ≤ (17316457502507/50000000000000 : ℝ)^389 := by
    have hnat : (900602939 : ℕ)^517*50000000000000^389 ≤ 17316457502507^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900602939 2000000000 17316457502507 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123990573/5000000000 : ℝ)^517 ≤ (801265599027/2500000000000 : ℝ)^389 := by
    have hnat : (2123990573 : ℕ)^517*2500000000000^389 ≤ 801265599027^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123990573 5000000000 801265599027 2500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186804901/5000000000 : ℝ), (900602939/2000000000 : ℝ), (2123990573/5000000000 : ℝ)] ![(1041139406637/3125000000000 : ℝ), (17316457502507/50000000000000 : ℝ), (801265599027/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186804901/5000000000 : ℝ)|^517 ≤ (1041139406637/3125000000000 : ℝ)^389
        have hw : |(2186804901/5000000000 : ℝ)|=(2186804901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900602939/2000000000 : ℝ)|^517 ≤ (17316457502507/50000000000000 : ℝ)^389
        have hw : |(900602939/2000000000 : ℝ)|=(900602939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123990573/5000000000 : ℝ)|^517 ≤ (801265599027/2500000000000 : ℝ)^389
        have hw : |(2123990573/5000000000 : ℝ)|=(2123990573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11259/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7011/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (11219/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (14560266215935979/100000000000000000000 : ℝ) := by
    have hpowers : (11219/100000 : ℝ)^8271 ≤ (14560266215935979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11219 : ℕ)^8271*100000000000000000000^2048 ≤ 14560266215935979^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 100000 14560266215935979 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/100000 : ℝ)) (X := (14560266215935979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14063/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (36261826912674277/100000000000000000000 : ℝ) := by
    have hpowers : (14063/100000 : ℝ)^8271 ≤ (36261826912674277/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14063 : ℕ)^8271*100000000000000000000^2048 ≤ 36261826912674277^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14063 100000 36261826912674277 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14063/100000 : ℝ)) (X := (36261826912674277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014560266215935979/50000000000000000000 : ℝ) ≤ (2000144196150683/2000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50014560266215935979/50000000000000000000 : ℝ)^2048 ≤ (2000144196150683/2000000000000000 : ℝ)^8271 := by
      have hnat : (50014560266215935979 : ℕ)^2048*2000000000000000^8271 ≤ 2000144196150683^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014560266215935979 50000000000000000000 2000144196150683 2000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144196150683/2000000000000000 : ℝ)) (X := (50014560266215935979/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253176380820538141/6250000000000000000 : ℝ) ≤ (1250157272024119/1250000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (6253176380820538141/6250000000000000000 : ℝ)^2048 ≤ (1250157272024119/1250000000000000 : ℝ)^8271 := by
      have hnat : (6253176380820538141 : ℕ)^2048*1250000000000000^8271 ≤ 1250157272024119^8271*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253176380820538141 6250000000000000000 1250157272024119 1250000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250157272024119/1250000000000000 : ℝ)) (X := (6253176380820538141/6250000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036261826912674277/50000000000000000000 : ℝ) ≤ (10001795371632489/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50036261826912674277/50000000000000000000 : ℝ)^2048 ≤ (10001795371632489/10000000000000000 : ℝ)^8271 := by
      have hnat : (50036261826912674277 : ℕ)^2048*10000000000000000^8271 ≤ 10001795371632489^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036261826912674277 50000000000000000000 10001795371632489 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001795371632489/10000000000000000 : ℝ)) (X := (50036261826912674277/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14560266215935979/100000000000000000000 : ℝ) ≤ ((14214998438995190527/14220000000000000000 : ℝ)+2*(537195439537/284400000000000 : ℝ)*(11219/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (14214998438995190527/14220000000000000000 : ℝ)+2*(537195439537/284400000000000 : ℝ)*(11219/100000 : ℝ)=(2000144196150683/2000000000000000 : ℝ) by norm_num, show 1+2*(14560266215935979/100000000000000000000 : ℝ)=(50014560266215935979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36261826912674277/100000000000000000000 : ℝ)+(14560266215935979/100000000000000000000 : ℝ) ≤ ((14214998438995190527/14220000000000000000 : ℝ)+(537195439537/284400000000000 : ℝ)*((14063/100000 : ℝ)+(11219/100000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (14214998438995190527/14220000000000000000 : ℝ)+(537195439537/284400000000000 : ℝ)*((14063/100000 : ℝ)+(11219/100000 : ℝ))=(1250157272024119/1250000000000000 : ℝ) by norm_num, show 1+(36261826912674277/100000000000000000000 : ℝ)+(14560266215935979/100000000000000000000 : ℝ)=(6253176380820538141/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36261826912674277/100000000000000000000 : ℝ) ≤ ((14214998438995190527/14220000000000000000 : ℝ)+2*(537195439537/284400000000000 : ℝ)*(14063/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (14214998438995190527/14220000000000000000 : ℝ)+2*(537195439537/284400000000000 : ℝ)*(14063/100000 : ℝ)=(10001795371632489/10000000000000000 : ℝ) by norm_num, show 1+2*(36261826912674277/100000000000000000000 : ℝ)=(50036261826912674277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14214998438995190527/14220000000000000000 : ℝ)*(X 1 0+X 2 0)+(537195439537/284400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (14214998438995190527/14220000000000000000 : ℝ)) (alpha := (537195439537/284400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14214998438995190527/14220000000000000000 : ℝ)*(X 0 1+X 2 1)+(537195439537/284400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (14214998438995190527/14220000000000000000 : ℝ)) (alpha := (537195439537/284400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14214998438995190527/14220000000000000000 : ℝ)*(X 0 2+X 1 2)+(537195439537/284400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (14214998438995190527/14220000000000000000 : ℝ)) (alpha := (537195439537/284400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098669851/5000000000 : ℝ)*X 0 0+(1348662557/2500000000 : ℝ)*X 0 1+(5264196861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069015463/2000000000 : ℝ)*X 1 0+(-1131765667/5000000000 : ℝ)*X 1 1+(2632098481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345077067/10000000000 : ℝ)*X 2 0+(5264197089/10000000000 : ℝ)*X 2 1+(-282941437/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874720007/2000000000 : ℝ)*X 0 0+(4247331367/10000000000 : ℝ)*X 0 1+(450366177/1000000000 : ℝ)*X 0 2+(874720007/2000000000 : ℝ)*X 1 0+(4247331367/10000000000 : ℝ)*X 1 1+(450366177/1000000000 : ℝ)*X 1 2+(874720007/2000000000 : ℝ)*X 2 0+(4247331367/10000000000 : ℝ)*X 2 1+(450366177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549336061/2500000000 : ℝ)*X 0 0+(5264526623/10000000000 : ℝ)*X 0 1+(215772789/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328046143/2500000000 : ℝ)*X 1 0+(-533352279/2500000000 : ℝ)*X 1 1+(5394319737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656092389/5000000000 : ℝ)*X 2 0+(5394319673/10000000000 : ℝ)*X 2 1+(-533352231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186804901/5000000000 : ℝ)*X 0 0+(900602939/2000000000 : ℝ)*X 0 1+(2123990573/5000000000 : ℝ)*X 0 2+(2186804901/5000000000 : ℝ)*X 1 0+(900602939/2000000000 : ℝ)*X 1 1+(2123990573/5000000000 : ℝ)*X 1 2+(2186804901/5000000000 : ℝ)*X 2 0+(900602939/2000000000 : ℝ)*X 2 1+(2123990573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177035691751849269954068763/39500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146125551/12500000000000 : ℝ)*(base19) + (864045377/100000000000000 : ℝ)*(base23) + (30805361/100000000000000 : ℝ)*(upper2) + (284036633/100000000000000 : ℝ)*(upper3) + (3700327/100000000000000 : ℝ)*(upper4) + (2891724250413807/50000000000000 : ℝ)*(major0) + (2891724250413807/50000000000000 : ℝ)*(major1) + (2891724250413807/50000000000000 : ℝ)*(major2) + (76656191704271/1000000000000 : ℝ)*(sp0) + (7665644668823111/100000000000000 : ℝ)*(sp1) + (3832822486891071/50000000000000 : ℝ)*(sp2) + (48765389496563/1250000000000 : ℝ)*(sp3) + (26667400419/100000000000000 : ℝ)*(sp4) + (19854705457/100000000000000 : ℝ)*(sp7) + (3901251014430497/100000000000000 : ℝ)*(f.failure) + (7665645837827519/100000000000000 : ℝ)*(f.sum) + (1616271693469/790000000000000000000000000 : ℝ)*base66 + (20970455658627079/79000000000000000000000000000000 : ℝ)*base68 + (234896461406372921/79000000000000000000000000000000 : ℝ)*base69 + (609855316671627079/79000000000000000000000000000000 : ℝ)*base72 + (644774520439/790000000000000000000000000 : ℝ)*base74 + (437179520246627079/79000000000000000000000000000000 : ℝ)*base76 + (566888349957372921/79000000000000000000000000000000 : ℝ)*base77 + (442621168937627079/79000000000000000000000000000000 : ℝ)*base80 + (2079833116949/790000000000000000000000000 : ℝ)*base82 + (14700503/5000000000000000000000 : ℝ)*base89 + (14700503/5000000000000000000000 : ℝ)*base91 + (14700503/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1271411865102978714639017273/118500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23592183/50000000000000 : ℝ)*(base8) + (239746831/100000000000000 : ℝ)*(lower2) + (64620673/100000000000000 : ℝ)*(lower4) + (13050537/100000000000000 : ℝ)*(lower5) + (5812821194936399/100000000000000 : ℝ)*(major0) + (5812821194936399/100000000000000 : ℝ)*(major1) + (5812821194936399/100000000000000 : ℝ)*(major2) + (2666577737/100000000000000 : ℝ)*(sp1) + (3828097041/50000000000000 : ℝ)*(sp2) + (994329691/25000000000000 : ℝ)*(sp3) + (7704577488631381/100000000000000 : ℝ)*(sp4) + (770457486923801/10000000000000 : ℝ)*(sp5) + (3852284939810833/50000000000000 : ℝ)*(sp6) + (3921060519097793/100000000000000 : ℝ)*(sp7) + (1960532248208279/50000000000000 : ℝ)*(f.failure) + (7704577535815747/100000000000000 : ℝ)*(f.sum) + (151594030268377/14220000000000000000000000000 : ℝ)*base66 + (4633095710097395303/158000000000000000000000000000000 : ℝ)*base68 + (4109066336823395303/158000000000000000000000000000000 : ℝ)*base70 + (11448768908932604697/158000000000000000000000000000000 : ℝ)*base71 + (395276945932163/14220000000000000000000000000 : ℝ)*base73 + (2807706942785395303/158000000000000000000000000000000 : ℝ)*base76 + (2752713454253395303/158000000000000000000000000000000 : ℝ)*base78 + (1295583682271395303/158000000000000000000000000000000 : ℝ)*base80 + (1159317001177/14220000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (41108721/2500000000000000000000 : ℝ)*base89 + (41108721/2500000000000000000000 : ℝ)*base91 + (41108721/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1079_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s7_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197374529/10000000000 : ℝ)*x 0 + (5394216559/10000000000 : ℝ)*x 1 + (5264607901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197374529/10000000000 : ℝ)^517 ≤ (13346223299121/100000000000000 : ℝ)^389 := by
    have hnat : (2197374529 : ℕ)^517*100000000000000^389 ≤ 13346223299121^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197374529 10000000000 13346223299121 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394216559/10000000000 : ℝ)^517 ≤ (11006765892881/25000000000000 : ℝ)^389 := by
    have hnat : (5394216559 : ℕ)^517*25000000000000^389 ≤ 11006765892881^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394216559 10000000000 11006765892881 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264607901/10000000000 : ℝ)^517 ≤ (21313356557649/50000000000000 : ℝ)^389 := by
    have hnat : (5264607901 : ℕ)^517*50000000000000^389 ≤ 21313356557649^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264607901 10000000000 21313356557649 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197374529/10000000000 : ℝ), (5394216559/10000000000 : ℝ), (5264607901/10000000000 : ℝ)] ![(13346223299121/100000000000000 : ℝ), (11006765892881/25000000000000 : ℝ), (21313356557649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197374529/10000000000 : ℝ)|^517 ≤ (13346223299121/100000000000000 : ℝ)^389
        have hw : |(-2197374529/10000000000 : ℝ)|=(2197374529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394216559/10000000000 : ℝ)|^517 ≤ (11006765892881/25000000000000 : ℝ)^389
        have hw : |(5394216559/10000000000 : ℝ)|=(5394216559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264607901/10000000000 : ℝ)|^517 ≤ (21313356557649/50000000000000 : ℝ)^389
        have hw : |(5264607901/10000000000 : ℝ)|=(5264607901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344969523/10000000000 : ℝ)*x 0 + (-452626331/2000000000 : ℝ)*x 1 + (5264608043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344969523/10000000000 : ℝ)^517 ≤ (43493657169829/100000000000000 : ℝ)^389 := by
    have hnat : (5344969523 : ℕ)^517*100000000000000^389 ≤ 43493657169829^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344969523 10000000000 43493657169829 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452626331/2000000000 : ℝ)^517 ≤ (3469907043079/25000000000000 : ℝ)^389 := by
    have hnat : (452626331 : ℕ)^517*25000000000000^389 ≤ 3469907043079^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452626331 2000000000 3469907043079 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264608043/10000000000 : ℝ)^517 ≤ (341013717147/800000000000 : ℝ)^389 := by
    have hnat : (5264608043 : ℕ)^517*800000000000^389 ≤ 341013717147^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264608043 10000000000 341013717147 800000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344969523/10000000000 : ℝ), (-452626331/2000000000 : ℝ), (5264608043/10000000000 : ℝ)] ![(43493657169829/100000000000000 : ℝ), (3469907043079/25000000000000 : ℝ), (341013717147/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344969523/10000000000 : ℝ)|^517 ≤ (43493657169829/100000000000000 : ℝ)^389
        have hw : |(5344969523/10000000000 : ℝ)|=(5344969523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452626331/2000000000 : ℝ)|^517 ≤ (3469907043079/25000000000000 : ℝ)^389
        have hw : |(-452626331/2000000000 : ℝ)|=(452626331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264608043/10000000000 : ℝ)|^517 ≤ (341013717147/800000000000 : ℝ)^389
        have hw : |(5264608043/10000000000 : ℝ)|=(5264608043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344969841/10000000000 : ℝ)*x 0 + (658075977/1250000000 : ℝ)*x 1 + (-565782883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344969841/10000000000 : ℝ)^517 ≤ (135917689403/312500000000 : ℝ)^389 := by
    have hnat : (5344969841 : ℕ)^517*312500000000^389 ≤ 135917689403^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344969841 10000000000 135917689403 312500000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658075977/1250000000 : ℝ)^517 ≤ (8525342440121/20000000000000 : ℝ)^389 := by
    have hnat : (658075977 : ℕ)^517*20000000000000^389 ≤ 8525342440121^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658075977 1250000000 8525342440121 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565782883/2500000000 : ℝ)^517 ≤ (3469906792437/25000000000000 : ℝ)^389 := by
    have hnat : (565782883 : ℕ)^517*25000000000000^389 ≤ 3469906792437^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565782883 2500000000 3469906792437 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344969841/10000000000 : ℝ), (658075977/1250000000 : ℝ), (-565782883/2500000000 : ℝ)] ![(135917689403/312500000000 : ℝ), (8525342440121/20000000000000 : ℝ), (3469906792437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344969841/10000000000 : ℝ)|^517 ≤ (135917689403/312500000000 : ℝ)^389
        have hw : |(5344969841/10000000000 : ℝ)|=(5344969841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658075977/1250000000 : ℝ)|^517 ≤ (8525342440121/20000000000000 : ℝ)^389
        have hw : |(658075977/1250000000 : ℝ)|=(658075977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565782883/2500000000 : ℝ)|^517 ≤ (3469906792437/25000000000000 : ℝ)^389
        have hw : |(-565782883/2500000000 : ℝ)|=(565782883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1093405429/2500000000 : ℝ)*x 0 + (849631723/2000000000 : ℝ)*x 1 + (1125707199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093405429/2500000000 : ℝ)^517 ≤ (6663316326379/20000000000000 : ℝ)^389 := by
    have hnat : (1093405429 : ℕ)^517*20000000000000^389 ≤ 6663316326379^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093405429 2500000000 6663316326379 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849631723/2000000000 : ℝ)^517 ≤ (50081880551/156250000000 : ℝ)^389 := by
    have hnat : (849631723 : ℕ)^517*156250000000^389 ≤ 50081880551^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849631723 2000000000 50081880551 156250000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125707199/2500000000 : ℝ)^517 ≤ (1385240591953/4000000000000 : ℝ)^389 := by
    have hnat : (1125707199 : ℕ)^517*4000000000000^389 ≤ 1385240591953^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125707199 2500000000 1385240591953 4000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093405429/2500000000 : ℝ), (849631723/2000000000 : ℝ), (1125707199/2500000000 : ℝ)] ![(6663316326379/20000000000000 : ℝ), (50081880551/156250000000 : ℝ), (1385240591953/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093405429/2500000000 : ℝ)|^517 ≤ (6663316326379/20000000000000 : ℝ)^389
        have hw : |(1093405429/2500000000 : ℝ)|=(1093405429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849631723/2000000000 : ℝ)|^517 ≤ (50081880551/156250000000 : ℝ)^389
        have hw : |(849631723/2000000000 : ℝ)|=(849631723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125707199/2500000000 : ℝ)|^517 ≤ (1385240591953/4000000000000 : ℝ)^389
        have hw : |(1125707199/2500000000 : ℝ)|=(1125707199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197379707/10000000000 : ℝ)*x 0 + (2632466579/5000000000 : ℝ)*x 1 + (1078778007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197379707/10000000000 : ℝ)^517 ≤ (13346265097309/100000000000000 : ℝ)^389 := by
    have hnat : (2197379707 : ℕ)^517*100000000000000^389 ≤ 13346265097309^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197379707 10000000000 13346265097309 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632466579/5000000000 : ℝ)^517 ≤ (42630213274699/100000000000000 : ℝ)^389 := by
    have hnat : (2632466579 : ℕ)^517*100000000000000^389 ≤ 42630213274699^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632466579 5000000000 42630213274699 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078778007/2000000000 : ℝ)^517 ≤ (22011760808147/50000000000000 : ℝ)^389 := by
    have hnat : (1078778007 : ℕ)^517*50000000000000^389 ≤ 22011760808147^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078778007 2000000000 22011760808147 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197379707/10000000000 : ℝ), (2632466579/5000000000 : ℝ), (1078778007/2000000000 : ℝ)] ![(13346265097309/100000000000000 : ℝ), (42630213274699/100000000000000 : ℝ), (22011760808147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197379707/10000000000 : ℝ)|^517 ≤ (13346265097309/100000000000000 : ℝ)^389
        have hw : |(-2197379707/10000000000 : ℝ)|=(2197379707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632466579/5000000000 : ℝ)|^517 ≤ (42630213274699/100000000000000 : ℝ)^389
        have hw : |(2632466579/5000000000 : ℝ)|=(2632466579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078778007/2000000000 : ℝ)|^517 ≤ (22011760808147/50000000000000 : ℝ)^389
        have hw : |(1078778007/2000000000 : ℝ)|=(1078778007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656145093/5000000000 : ℝ)*x 0 + (-133365599/625000000 : ℝ)*x 1 + (1078778007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656145093/5000000000 : ℝ)^517 ≤ (1725623604671/4000000000000 : ℝ)^389 := by
    have hnat : (2656145093 : ℕ)^517*4000000000000^389 ≤ 1725623604671^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656145093 5000000000 1725623604671 4000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133365599/625000000 : ℝ)^517 ≤ (2567177652211/20000000000000 : ℝ)^389 := by
    have hnat : (133365599 : ℕ)^517*20000000000000^389 ≤ 2567177652211^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133365599 625000000 2567177652211 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078778007/2000000000 : ℝ)^517 ≤ (22011760808147/50000000000000 : ℝ)^389 := by
    have hnat : (1078778007 : ℕ)^517*50000000000000^389 ≤ 22011760808147^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078778007 2000000000 22011760808147 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656145093/5000000000 : ℝ), (-133365599/625000000 : ℝ), (1078778007/2000000000 : ℝ)] ![(1725623604671/4000000000000 : ℝ), (2567177652211/20000000000000 : ℝ), (22011760808147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656145093/5000000000 : ℝ)|^517 ≤ (1725623604671/4000000000000 : ℝ)^389
        have hw : |(2656145093/5000000000 : ℝ)|=(2656145093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133365599/625000000 : ℝ)|^517 ≤ (2567177652211/20000000000000 : ℝ)^389
        have hw : |(-133365599/625000000 : ℝ)|=(133365599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078778007/2000000000 : ℝ)|^517 ≤ (22011760808147/50000000000000 : ℝ)^389
        have hw : |(1078778007/2000000000 : ℝ)|=(1078778007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312290187/10000000000 : ℝ)*x 0 + (2696945017/5000000000 : ℝ)*x 1 + (-2133849583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312290187/10000000000 : ℝ)^517 ≤ (2696286882973/6250000000000 : ℝ)^389 := by
    have hnat : (5312290187 : ℕ)^517*6250000000000^389 ≤ 2696286882973^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312290187 10000000000 2696286882973 6250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696945017/5000000000 : ℝ)^517 ≤ (44023521605447/100000000000000 : ℝ)^389 := by
    have hnat : (2696945017 : ℕ)^517*100000000000000^389 ≤ 44023521605447^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696945017 5000000000 44023521605447 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133849583/10000000000 : ℝ)^517 ≤ (12835888253061/100000000000000 : ℝ)^389 := by
    have hnat : (2133849583 : ℕ)^517*100000000000000^389 ≤ 12835888253061^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133849583 10000000000 12835888253061 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312290187/10000000000 : ℝ), (2696945017/5000000000 : ℝ), (-2133849583/10000000000 : ℝ)] ![(2696286882973/6250000000000 : ℝ), (44023521605447/100000000000000 : ℝ), (12835888253061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312290187/10000000000 : ℝ)|^517 ≤ (2696286882973/6250000000000 : ℝ)^389
        have hw : |(5312290187/10000000000 : ℝ)|=(5312290187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696945017/5000000000 : ℝ)|^517 ≤ (44023521605447/100000000000000 : ℝ)^389
        have hw : |(2696945017/5000000000 : ℝ)|=(2696945017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133849583/10000000000 : ℝ)|^517 ≤ (12835888253061/100000000000000 : ℝ)^389
        have hw : |(-2133849583/10000000000 : ℝ)|=(2133849583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s7_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2186815773/5000000000 : ℝ)*x 0 + (2251094939/5000000000 : ℝ)*x 1 + (66387499/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186815773/5000000000 : ℝ)^517 ≤ (3331668115269/10000000000000 : ℝ)^389 := by
    have hnat : (2186815773 : ℕ)^517*10000000000000^389 ≤ 3331668115269^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186815773 5000000000 3331668115269 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251094939/5000000000 : ℝ)^517 ≤ (2164030259959/6250000000000 : ℝ)^389 := by
    have hnat : (2251094939 : ℕ)^517*6250000000000^389 ≤ 2164030259959^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251094939 5000000000 2164030259959 6250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66387499/156250000 : ℝ)^517 ≤ (32058834679363/100000000000000 : ℝ)^389 := by
    have hnat : (66387499 : ℕ)^517*100000000000000^389 ≤ 32058834679363^389*156250000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66387499 156250000 32058834679363 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186815773/5000000000 : ℝ), (2251094939/5000000000 : ℝ), (66387499/156250000 : ℝ)] ![(3331668115269/10000000000000 : ℝ), (2164030259959/6250000000000 : ℝ), (32058834679363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186815773/5000000000 : ℝ)|^517 ≤ (3331668115269/10000000000000 : ℝ)^389
        have hw : |(2186815773/5000000000 : ℝ)|=(2186815773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251094939/5000000000 : ℝ)|^517 ≤ (2164030259959/6250000000000 : ℝ)^389
        have hw : |(2251094939/5000000000 : ℝ)|=(2251094939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66387499/156250000 : ℝ)|^517 ≤ (32058834679363/100000000000000 : ℝ)^389
        have hw : |(66387499/156250000 : ℝ)|=(66387499/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2817/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11259/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (14771058667515379/100000000000000000000 : ℝ) := by
    have hpowers : (11259/100000 : ℝ)^8271 ≤ (14771058667515379/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11259 : ℕ)^8271*100000000000000000000^2048 ≤ 14771058667515379^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11259 100000 14771058667515379 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11259/100000 : ℝ)) (X := (14771058667515379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7011/50000 : ℝ) ^ (8271/2048 : ℝ) ≤ (17918378917111249/50000000000000000000 : ℝ) := by
    have hpowers : (7011/50000 : ℝ)^8271 ≤ (17918378917111249/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7011 : ℕ)^8271*50000000000000000000^2048 ≤ 17918378917111249^2048*50000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7011 50000 17918378917111249 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7011/50000 : ℝ)) (X := (17918378917111249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014771058667515379/50000000000000000000 : ℝ) ≤ (5000365708702119/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50014771058667515379/50000000000000000000 : ℝ)^2048 ≤ (5000365708702119/5000000000000000 : ℝ)^8271 := by
      have hnat : (50014771058667515379 : ℕ)^2048*5000000000000000^8271 ≤ 5000365708702119^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014771058667515379 50000000000000000000 5000365708702119 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000365708702119/5000000000000000 : ℝ)) (X := (50014771058667515379/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050607816501737877/100000000000000000000 : ℝ) ≤ (10001252872467197/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100050607816501737877/100000000000000000000 : ℝ)^2048 ≤ (10001252872467197/10000000000000000 : ℝ)^8271 := by
      have hnat : (100050607816501737877 : ℕ)^2048*10000000000000000^8271 ≤ 10001252872467197^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050607816501737877 100000000000000000000 10001252872467197 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001252872467197/10000000000000000 : ℝ)) (X := (100050607816501737877/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017918378917111249/25000000000000000000 : ℝ) ≤ (2500443581882539/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25017918378917111249/25000000000000000000 : ℝ)^2048 ≤ (2500443581882539/2500000000000000 : ℝ)^8271 := by
      have hnat : (25017918378917111249 : ℕ)^2048*2500000000000000^8271 ≤ 2500443581882539^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017918378917111249 25000000000000000000 2500443581882539 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500443581882539/2500000000000000 : ℝ)) (X := (25017918378917111249/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14771058667515379/100000000000000000000 : ℝ) ≤ ((191807491535973603/191875000000000000 : ℝ)+2*(521455062959/276300000000000 : ℝ)*(11259/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (191807491535973603/191875000000000000 : ℝ)+2*(521455062959/276300000000000 : ℝ)*(11259/100000 : ℝ)=(5000365708702119/5000000000000000 : ℝ) by norm_num, show 1+2*(14771058667515379/100000000000000000000 : ℝ)=(50014771058667515379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17918378917111249/50000000000000000000 : ℝ)+(14771058667515379/100000000000000000000 : ℝ) ≤ ((191807491535973603/191875000000000000 : ℝ)+(521455062959/276300000000000 : ℝ)*((7011/50000 : ℝ)+(11259/100000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (191807491535973603/191875000000000000 : ℝ)+(521455062959/276300000000000 : ℝ)*((7011/50000 : ℝ)+(11259/100000 : ℝ))=(10001252872467197/10000000000000000 : ℝ) by norm_num, show 1+(17918378917111249/50000000000000000000 : ℝ)+(14771058667515379/100000000000000000000 : ℝ)=(100050607816501737877/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17918378917111249/50000000000000000000 : ℝ) ≤ ((191807491535973603/191875000000000000 : ℝ)+2*(521455062959/276300000000000 : ℝ)*(7011/50000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (191807491535973603/191875000000000000 : ℝ)+2*(521455062959/276300000000000 : ℝ)*(7011/50000 : ℝ)=(2500443581882539/2500000000000000 : ℝ) by norm_num, show 1+2*(17918378917111249/50000000000000000000 : ℝ)=(25017918378917111249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (191807491535973603/191875000000000000 : ℝ)*(X 1 0+X 2 0)+(521455062959/276300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (191807491535973603/191875000000000000 : ℝ)) (alpha := (521455062959/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (191807491535973603/191875000000000000 : ℝ)*(X 0 1+X 2 1)+(521455062959/276300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (191807491535973603/191875000000000000 : ℝ)) (alpha := (521455062959/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (191807491535973603/191875000000000000 : ℝ)*(X 0 2+X 1 2)+(521455062959/276300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (191807491535973603/191875000000000000 : ℝ)) (alpha := (521455062959/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2197374529/10000000000 : ℝ)*X 0 0+(5394216559/10000000000 : ℝ)*X 0 1+(5264607901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344969523/10000000000 : ℝ)*X 1 0+(-452626331/2000000000 : ℝ)*X 1 1+(5264608043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344969841/10000000000 : ℝ)*X 2 0+(658075977/1250000000 : ℝ)*X 2 1+(-565782883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093405429/2500000000 : ℝ)*X 0 0+(849631723/2000000000 : ℝ)*X 0 1+(1125707199/2500000000 : ℝ)*X 0 2+(1093405429/2500000000 : ℝ)*X 1 0+(849631723/2000000000 : ℝ)*X 1 1+(1125707199/2500000000 : ℝ)*X 1 2+(1093405429/2500000000 : ℝ)*X 2 0+(849631723/2000000000 : ℝ)*X 2 1+(1125707199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2197379707/10000000000 : ℝ)*X 0 0+(2632466579/5000000000 : ℝ)*X 0 1+(1078778007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656145093/5000000000 : ℝ)*X 1 0+(-133365599/625000000 : ℝ)*X 1 1+(1078778007/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312290187/10000000000 : ℝ)*X 2 0+(2696945017/5000000000 : ℝ)*X 2 1+(-2133849583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186815773/5000000000 : ℝ)*X 0 0+(2251094939/5000000000 : ℝ)*X 0 1+(66387499/156250000 : ℝ)*X 0 2+(2186815773/5000000000 : ℝ)*X 1 0+(2251094939/5000000000 : ℝ)*X 1 1+(66387499/156250000 : ℝ)*X 1 2+(2186815773/5000000000 : ℝ)*X 2 0+(2251094939/5000000000 : ℝ)*X 2 1+(66387499/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3285908455093933563010123/1439062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (95689963/20000000000000 : ℝ)*(base19) + (82551497/12500000000000 : ℝ)*(base23) + (76288389/50000000000000 : ℝ)*(lower2) + (33542973/100000000000000 : ℝ)*(upper5) + (2273875086367/39062500000 : ℝ)*(major0) + (2273875086367/39062500000 : ℝ)*(major1) + (2273875086367/39062500000 : ℝ)*(major2) + (30862201417239/400000000000 : ℝ)*(sp0) + (1543115175054053/20000000000000 : ℝ)*(sp1) + (1543115412819489/20000000000000 : ℝ)*(sp2) + (1963326662060003/50000000000000 : ℝ)*(sp3) + (3421274959/12500000000000 : ℝ)*(sp4) + (685394671/50000000000000 : ℝ)*(sp5) + (9317457353/100000000000000 : ℝ)*(sp7) + (49083283019717/1250000000000 : ℝ)*(f.failure) + (7715577724509421/100000000000000 : ℝ)*(f.sum) + (5477759579149/690750000000000000000000000 : ℝ)*base65 + (13584963706128499/4317187500000000000000000000000 : ℝ)*base68 + (5442926209102751/4317187500000000000000000000000 : ℝ)*base69 + (200342916501077377/8634375000000000000000000000000 : ℝ)*base71 + (16465004673013/2763000000000000000000000000 : ℝ)*base73 + (29852594613564877/8634375000000000000000000000000 : ℝ)*base75 + (174292790938596127/8634375000000000000000000000000 : ℝ)*base77 + (11246998575954781/1079296875000000000000000000000 : ℝ)*base80 + (1416334527209/690750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (171283/62500000000000000000 : ℝ)*base89 + (171283/62500000000000000000 : ℝ)*base91 + (171283/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21082228587723361853981201/2878125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1347710331/100000000000000 : ℝ)*(base19) + (734424019/50000000000000 : ℝ)*(base23) + (36476659/25000000000000 : ℝ)*(upper3) + (1696753/3125000000000 : ℝ)*(lower4) + (74183471/50000000000000 : ℝ)*(upper5) + (1170101529948287/20000000000000 : ℝ)*(major0) + (1170101529948287/20000000000000 : ℝ)*(major1) + (1170101529948287/20000000000000 : ℝ)*(major2) + (18365417933/50000000000000 : ℝ)*(sp1) + (39570263387/100000000000000 : ℝ)*(sp2) + (7754528992508079/100000000000000 : ℝ)*(sp4) + (3877245456980941/50000000000000 : ℝ)*(sp5) + (1550897590679331/20000000000000 : ℝ)*(sp6) + (1973243031404273/50000000000000 : ℝ)*(sp7) + (1973243031404273/50000000000000 : ℝ)*(f.failure) + (7754528992508079/100000000000000 : ℝ)*(f.sum) + (3172266170609/690750000000000000000000000 : ℝ)*base66 + (308365974543693799/34537500000000000000000000000000 : ℝ)*base67 + (106312448798531299/34537500000000000000000000000000 : ℝ)*base69 + (80690864346093799/34537500000000000000000000000000 : ℝ)*base71 + (4637027318177/2763000000000000000000000000 : ℝ)*base74 + (210925730089668799/34537500000000000000000000000000 : ℝ)*base75 + (308478318192768799/34537500000000000000000000000000 : ℝ)*base77 + (504034963675556201/34537500000000000000000000000000 : ℝ)*base80 + (1426932494251/345375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (21174727/2500000000000000000000 : ℝ)*base89 + (21174727/2500000000000000000000 : ℝ)*base91 + (21174727/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1079_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s8_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-549345411/2500000000 : ℝ)*x 0 + (1348530463/2500000000 : ℝ)*x 1 + (5264698031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549345411/2500000000 : ℝ)^517 ≤ (2669256146659/20000000000000 : ℝ)^389 := by
    have hnat : (549345411 : ℕ)^517*20000000000000^389 ≤ 2669256146659^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549345411 2500000000 2669256146659 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348530463/2500000000 : ℝ)^517 ≤ (22013018117049/50000000000000 : ℝ)^389 := by
    have hnat : (1348530463 : ℕ)^517*50000000000000^389 ≤ 22013018117049^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348530463 2500000000 22013018117049 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264698031/10000000000 : ℝ)^517 ≤ (42627683016173/100000000000000 : ℝ)^389 := by
    have hnat : (5264698031 : ℕ)^517*100000000000000^389 ≤ 42627683016173^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264698031 10000000000 42627683016173 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549345411/2500000000 : ℝ), (1348530463/2500000000 : ℝ), (5264698031/10000000000 : ℝ)] ![(2669256146659/20000000000000 : ℝ), (22013018117049/50000000000000 : ℝ), (42627683016173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549345411/2500000000 : ℝ)|^517 ≤ (2669256146659/20000000000000 : ℝ)^389
        have hw : |(-549345411/2500000000 : ℝ)|=(549345411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348530463/2500000000 : ℝ)|^517 ≤ (22013018117049/50000000000000 : ℝ)^389
        have hw : |(1348530463/2500000000 : ℝ)|=(1348530463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264698031/10000000000 : ℝ)|^517 ≤ (42627683016173/100000000000000 : ℝ)^389
        have hw : |(5264698031/10000000000 : ℝ)|=(5264698031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672473149/5000000000 : ℝ)*x 0 + (-226304331/1000000000 : ℝ)*x 1 + (52646983/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672473149/5000000000 : ℝ)^517 ≤ (2174670299723/5000000000000 : ℝ)^389 := by
    have hnat : (2672473149 : ℕ)^517*5000000000000^389 ≤ 2174670299723^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672473149 5000000000 2174670299723 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226304331/1000000000 : ℝ)^517 ≤ (13878908080061/100000000000000 : ℝ)^389 := by
    have hnat : (226304331 : ℕ)^517*100000000000000^389 ≤ 13878908080061^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226304331 1000000000 13878908080061 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52646983/100000000 : ℝ)^517 ≤ (21313842955463/50000000000000 : ℝ)^389 := by
    have hnat : (52646983 : ℕ)^517*50000000000000^389 ≤ 21313842955463^389*100000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52646983 100000000 21313842955463 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672473149/5000000000 : ℝ), (-226304331/1000000000 : ℝ), (52646983/100000000 : ℝ)] ![(2174670299723/5000000000000 : ℝ), (13878908080061/100000000000000 : ℝ), (21313842955463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672473149/5000000000 : ℝ)|^517 ≤ (2174670299723/5000000000000 : ℝ)^389
        have hw : |(2672473149/5000000000 : ℝ)|=(2672473149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226304331/1000000000 : ℝ)|^517 ≤ (13878908080061/100000000000000 : ℝ)^389
        have hw : |(-226304331/1000000000 : ℝ)|=(226304331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52646983/100000000 : ℝ)|^517 ≤ (21313842955463/50000000000000 : ℝ)^389
        have hw : |(52646983/100000000 : ℝ)|=(52646983/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344946091/10000000000 : ℝ)*x 0 + (1316174631/2500000000 : ℝ)*x 1 + (-226304329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344946091/10000000000 : ℝ)^517 ≤ (5436675469473/12500000000000 : ℝ)^389 := by
    have hnat : (5344946091 : ℕ)^517*12500000000000^389 ≤ 5436675469473^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344946091 10000000000 5436675469473 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316174631/2500000000 : ℝ)^517 ≤ (21313844160713/50000000000000 : ℝ)^389 := by
    have hnat : (1316174631 : ℕ)^517*50000000000000^389 ≤ 21313844160713^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316174631 2500000000 21313844160713 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226304329/1000000000 : ℝ)^517 ≤ (3469726979261/25000000000000 : ℝ)^389 := by
    have hnat : (226304329 : ℕ)^517*25000000000000^389 ≤ 3469726979261^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226304329 1000000000 3469726979261 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344946091/10000000000 : ℝ), (1316174631/2500000000 : ℝ), (-226304329/1000000000 : ℝ)] ![(5436675469473/12500000000000 : ℝ), (21313844160713/50000000000000 : ℝ), (3469726979261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344946091/10000000000 : ℝ)|^517 ≤ (5436675469473/12500000000000 : ℝ)^389
        have hw : |(5344946091/10000000000 : ℝ)|=(5344946091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316174631/2500000000 : ℝ)|^517 ≤ (21313844160713/50000000000000 : ℝ)^389
        have hw : |(1316174631/2500000000 : ℝ)|=(1316174631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226304329/1000000000 : ℝ)|^517 ≤ (3469726979261/25000000000000 : ℝ)^389
        have hw : |(-226304329/1000000000 : ℝ)|=(226304329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (874725269/2000000000 : ℝ)*x 0 + (212416979/500000000 : ℝ)*x 1 + (4502646677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874725269/2000000000 : ℝ)^517 ≤ (6663325699353/20000000000000 : ℝ)^389 := by
    have hnat : (874725269 : ℕ)^517*20000000000000^389 ≤ 6663325699353^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874725269 2000000000 6663325699353 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212416979/500000000 : ℝ)^517 ≤ (16027109112973/50000000000000 : ℝ)^389 := by
    have hnat : (212416979 : ℕ)^517*50000000000000^389 ≤ 16027109112973^389*500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212416979 500000000 16027109112973 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502646677/10000000000 : ℝ)^517 ≤ (34629153255741/100000000000000 : ℝ)^389 := by
    have hnat : (4502646677 : ℕ)^517*100000000000000^389 ≤ 34629153255741^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502646677 10000000000 34629153255741 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874725269/2000000000 : ℝ), (212416979/500000000 : ℝ), (4502646677/10000000000 : ℝ)] ![(6663325699353/20000000000000 : ℝ), (16027109112973/50000000000000 : ℝ), (34629153255741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874725269/2000000000 : ℝ)|^517 ≤ (6663325699353/20000000000000 : ℝ)^389
        have hw : |(874725269/2000000000 : ℝ)|=(874725269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212416979/500000000 : ℝ)|^517 ≤ (16027109112973/50000000000000 : ℝ)^389
        have hw : |(212416979/500000000 : ℝ)|=(212416979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502646677/10000000000 : ℝ)|^517 ≤ (34629153255741/100000000000000 : ℝ)^389
        have hw : |(4502646677/10000000000 : ℝ)|=(4502646677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-219738661/1000000000 : ℝ)*x 0 + (5265022389/10000000000 : ℝ)*x 1 + (2696898187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219738661/1000000000 : ℝ)^517 ≤ (2669264164041/20000000000000 : ℝ)^389 := by
    have hnat : (219738661 : ℕ)^517*20000000000000^389 ≤ 2669264164041^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219738661 1000000000 2669264164041 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265022389/10000000000 : ℝ)^517 ≤ (42631173520809/100000000000000 : ℝ)^389 := by
    have hnat : (5265022389 : ℕ)^517*100000000000000^389 ≤ 42631173520809^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265022389 10000000000 42631173520809 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696898187/5000000000 : ℝ)^517 ≤ (44022505645593/100000000000000 : ℝ)^389 := by
    have hnat : (2696898187 : ℕ)^517*100000000000000^389 ≤ 44022505645593^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696898187 5000000000 44022505645593 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219738661/1000000000 : ℝ), (5265022389/10000000000 : ℝ), (2696898187/5000000000 : ℝ)] ![(2669264164041/20000000000000 : ℝ), (42631173520809/100000000000000 : ℝ), (44022505645593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219738661/1000000000 : ℝ)|^517 ≤ (2669264164041/20000000000000 : ℝ)^389
        have hw : |(-219738661/1000000000 : ℝ)|=(219738661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265022389/10000000000 : ℝ)|^517 ≤ (42631173520809/100000000000000 : ℝ)^389
        have hw : |(5265022389/10000000000 : ℝ)|=(5265022389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696898187/5000000000 : ℝ)|^517 ≤ (44022505645593/100000000000000 : ℝ)^389
        have hw : |(2696898187/5000000000 : ℝ)|=(2696898187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312313667/10000000000 : ℝ)*x 0 + (-1066972431/5000000000 : ℝ)*x 1 + (5393796447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312313667/10000000000 : ℝ)^517 ≤ (5392605443647/12500000000000 : ℝ)^389 := by
    have hnat : (5312313667 : ℕ)^517*12500000000000^389 ≤ 5392605443647^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312313667 10000000000 5392605443647 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066972431/5000000000 : ℝ)^517 ≤ (802290624203/6250000000000 : ℝ)^389 := by
    have hnat : (1066972431 : ℕ)^517*6250000000000^389 ≤ 802290624203^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066972431 5000000000 802290624203 6250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393796447/10000000000 : ℝ)^517 ≤ (8804501287489/20000000000000 : ℝ)^389 := by
    have hnat : (5393796447 : ℕ)^517*20000000000000^389 ≤ 8804501287489^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393796447 10000000000 8804501287489 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312313667/10000000000 : ℝ), (-1066972431/5000000000 : ℝ), (5393796447/10000000000 : ℝ)] ![(5392605443647/12500000000000 : ℝ), (802290624203/6250000000000 : ℝ), (8804501287489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312313667/10000000000 : ℝ)|^517 ≤ (5392605443647/12500000000000 : ℝ)^389
        have hw : |(5312313667/10000000000 : ℝ)|=(5312313667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066972431/5000000000 : ℝ)|^517 ≤ (802290624203/6250000000000 : ℝ)^389
        have hw : |(-1066972431/5000000000 : ℝ)|=(1066972431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393796447/10000000000 : ℝ)|^517 ≤ (8804501287489/20000000000000 : ℝ)^389
        have hw : |(5393796447/10000000000 : ℝ)|=(5393796447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656156527/5000000000 : ℝ)*x 0 + (5393796389/10000000000 : ℝ)*x 1 + (-2133945769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656156527/5000000000 : ℝ)^517 ≤ (43140836933011/100000000000000 : ℝ)^389 := by
    have hnat : (2656156527 : ℕ)^517*100000000000000^389 ≤ 43140836933011^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656156527 5000000000 43140836933011 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393796389/10000000000 : ℝ)^517 ≤ (44022505808303/100000000000000 : ℝ)^389 := by
    have hnat : (5393796389 : ℕ)^517*100000000000000^389 ≤ 44022505808303^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393796389 10000000000 44022505808303 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133945769/10000000000 : ℝ)^517 ≤ (12836657238563/100000000000000 : ℝ)^389 := by
    have hnat : (2133945769 : ℕ)^517*100000000000000^389 ≤ 12836657238563^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133945769 10000000000 12836657238563 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656156527/5000000000 : ℝ), (5393796389/10000000000 : ℝ), (-2133945769/10000000000 : ℝ)] ![(43140836933011/100000000000000 : ℝ), (44022505808303/100000000000000 : ℝ), (12836657238563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656156527/5000000000 : ℝ)|^517 ≤ (43140836933011/100000000000000 : ℝ)^389
        have hw : |(2656156527/5000000000 : ℝ)|=(2656156527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393796389/10000000000 : ℝ)|^517 ≤ (44022505808303/100000000000000 : ℝ)^389
        have hw : |(5393796389/10000000000 : ℝ)|=(5393796389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133945769/10000000000 : ℝ)|^517 ≤ (12836657238563/100000000000000 : ℝ)^389
        have hw : |(-2133945769/10000000000 : ℝ)|=(2133945769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s8_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4373635731/10000000000 : ℝ)*x 0 + (180080377/400000000 : ℝ)*x 1 + (2124489817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373635731/10000000000 : ℝ)^517 ≤ (33316723522451/100000000000000 : ℝ)^389 := by
    have hnat : (4373635731 : ℕ)^517*100000000000000^389 ≤ 33316723522451^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373635731 10000000000 33316723522451 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180080377/400000000 : ℝ)^517 ≤ (17311319865709/50000000000000 : ℝ)^389 := by
    have hnat : (180080377 : ℕ)^517*50000000000000^389 ≤ 17311319865709^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180080377 400000000 17311319865709 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124489817/5000000000 : ℝ)^517 ≤ (32060636736917/100000000000000 : ℝ)^389 := by
    have hnat : (2124489817 : ℕ)^517*100000000000000^389 ≤ 32060636736917^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124489817 5000000000 32060636736917 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373635731/10000000000 : ℝ), (180080377/400000000 : ℝ), (2124489817/5000000000 : ℝ)] ![(33316723522451/100000000000000 : ℝ), (17311319865709/50000000000000 : ℝ), (32060636736917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373635731/10000000000 : ℝ)|^517 ≤ (33316723522451/100000000000000 : ℝ)^389
        have hw : |(4373635731/10000000000 : ℝ)|=(4373635731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180080377/400000000 : ℝ)|^517 ≤ (17311319865709/50000000000000 : ℝ)^389
        have hw : |(180080377/400000000 : ℝ)|=(180080377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124489817/5000000000 : ℝ)|^517 ≤ (32060636736917/100000000000000 : ℝ)^389
        have hw : |(2124489817/5000000000 : ℝ)|=(2124489817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1127/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2817/25000 : ℝ) ^ (8271/2048 : ℝ) ≤ (7409400837907889/50000000000000000000 : ℝ) := by
    have hpowers : (2817/25000 : ℝ)^8271 ≤ (7409400837907889/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2817 : ℕ)^8271*50000000000000000000^2048 ≤ 7409400837907889^2048*25000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 25000 7409400837907889 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/25000 : ℝ)) (X := (7409400837907889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14013/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (17871977012547417/50000000000000000000 : ℝ) := by
    have hpowers : (14013/100000 : ℝ)^8271 ≤ (17871977012547417/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14013 : ℕ)^8271*50000000000000000000^2048 ≤ 17871977012547417^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14013 100000 17871977012547417 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14013/100000 : ℝ)) (X := (17871977012547417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007409400837907889/25000000000000000000 : ℝ) ≤ (5000366890613839/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25007409400837907889/25000000000000000000 : ℝ)^2048 ≤ (5000366890613839/5000000000000000 : ℝ)^8271 := by
      have hnat : (25007409400837907889 : ℕ)^2048*5000000000000000^8271 ≤ 5000366890613839^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007409400837907889 25000000000000000000 5000366890613839 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000366890613839/5000000000000000 : ℝ)) (X := (25007409400837907889/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012640688925227653/25000000000000000000 : ℝ) ≤ (10001251757131537/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25012640688925227653/25000000000000000000 : ℝ)^2048 ≤ (10001251757131537/10000000000000000 : ℝ)^8271 := by
      have hnat : (25012640688925227653 : ℕ)^2048*10000000000000000^8271 ≤ 10001251757131537^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012640688925227653 25000000000000000000 10001251757131537 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001251757131537/10000000000000000 : ℝ)) (X := (25012640688925227653/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017871977012547417/25000000000000000000 : ℝ) ≤ (2500442433258849/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25017871977012547417/25000000000000000000 : ℝ)^2048 ≤ (2500442433258849/2500000000000000 : ℝ)^8271 := by
      have hnat : (25017871977012547417 : ℕ)^2048*2500000000000000^8271 ≤ 2500442433258849^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017871977012547417 25000000000000000000 2500442433258849 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500442433258849/2500000000000000 : ℝ)) (X := (25017871977012547417/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7409400837907889/50000000000000000000 : ℝ) ≤ ((1524463395805589427/1525000000000000000 : ℝ)+2*(517975903859/274500000000000 : ℝ)*(2817/25000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (1524463395805589427/1525000000000000000 : ℝ)+2*(517975903859/274500000000000 : ℝ)*(2817/25000 : ℝ)=(5000366890613839/5000000000000000 : ℝ) by norm_num, show 1+2*(7409400837907889/50000000000000000000 : ℝ)=(25007409400837907889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17871977012547417/50000000000000000000 : ℝ)+(7409400837907889/50000000000000000000 : ℝ) ≤ ((1524463395805589427/1525000000000000000 : ℝ)+(517975903859/274500000000000 : ℝ)*((14013/100000 : ℝ)+(2817/25000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (1524463395805589427/1525000000000000000 : ℝ)+(517975903859/274500000000000 : ℝ)*((14013/100000 : ℝ)+(2817/25000 : ℝ))=(10001251757131537/10000000000000000 : ℝ) by norm_num, show 1+(17871977012547417/50000000000000000000 : ℝ)+(7409400837907889/50000000000000000000 : ℝ)=(25012640688925227653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17871977012547417/50000000000000000000 : ℝ) ≤ ((1524463395805589427/1525000000000000000 : ℝ)+2*(517975903859/274500000000000 : ℝ)*(14013/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (1524463395805589427/1525000000000000000 : ℝ)+2*(517975903859/274500000000000 : ℝ)*(14013/100000 : ℝ)=(2500442433258849/2500000000000000 : ℝ) by norm_num, show 1+2*(17871977012547417/50000000000000000000 : ℝ)=(25017871977012547417/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1524463395805589427/1525000000000000000 : ℝ)*(X 1 0+X 2 0)+(517975903859/274500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (1524463395805589427/1525000000000000000 : ℝ)) (alpha := (517975903859/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1524463395805589427/1525000000000000000 : ℝ)*(X 0 1+X 2 1)+(517975903859/274500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (1524463395805589427/1525000000000000000 : ℝ)) (alpha := (517975903859/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1524463395805589427/1525000000000000000 : ℝ)*(X 0 2+X 1 2)+(517975903859/274500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (1524463395805589427/1525000000000000000 : ℝ)) (alpha := (517975903859/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549345411/2500000000 : ℝ)*X 0 0+(1348530463/2500000000 : ℝ)*X 0 1+(5264698031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672473149/5000000000 : ℝ)*X 1 0+(-226304331/1000000000 : ℝ)*X 1 1+(52646983/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344946091/10000000000 : ℝ)*X 2 0+(1316174631/2500000000 : ℝ)*X 2 1+(-226304329/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874725269/2000000000 : ℝ)*X 0 0+(212416979/500000000 : ℝ)*X 0 1+(4502646677/10000000000 : ℝ)*X 0 2+(874725269/2000000000 : ℝ)*X 1 0+(212416979/500000000 : ℝ)*X 1 1+(4502646677/10000000000 : ℝ)*X 1 2+(874725269/2000000000 : ℝ)*X 2 0+(212416979/500000000 : ℝ)*X 2 1+(4502646677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219738661/1000000000 : ℝ)*X 0 0+(5265022389/10000000000 : ℝ)*X 0 1+(2696898187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312313667/10000000000 : ℝ)*X 1 0+(-1066972431/5000000000 : ℝ)*X 1 1+(5393796447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656156527/5000000000 : ℝ)*X 2 0+(5393796389/10000000000 : ℝ)*X 2 1+(-2133945769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373635731/10000000000 : ℝ)*X 0 0+(180080377/400000000 : ℝ)*X 0 1+(2124489817/5000000000 : ℝ)*X 0 2+(4373635731/10000000000 : ℝ)*X 1 0+(180080377/400000000 : ℝ)*X 1 1+(2124489817/5000000000 : ℝ)*X 1 2+(4373635731/10000000000 : ℝ)*X 2 0+(180080377/400000000 : ℝ)*X 2 1+(2124489817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (670745590462670751421/305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218244943/50000000000000 : ℝ)*(base19) + (980443/1562500000000 : ℝ)*(base23) + (117316777/100000000000000 : ℝ)*(upper3) + (39822129/100000000000000 : ℝ)*(upper4) + (38877251/100000000000000 : ℝ)*(upper5) + (1165887917317977/20000000000000 : ℝ)*(major0) + (1165887917317977/20000000000000 : ℝ)*(major1) + (1165887917317977/20000000000000 : ℝ)*(major2) + (7726581570391947/100000000000000 : ℝ)*(sp0) + (3863302078331081/50000000000000 : ℝ)*(sp1) + (482912783150231/6250000000000 : ℝ)*(sp2) + (3932263848034001/100000000000000 : ℝ)*(sp3) + (23022760101/100000000000000 : ℝ)*(sp4) + (10658688187/100000000000000 : ℝ)*(sp7) + (983068626680547/25000000000000 : ℝ)*(f.failure) + (482912787072003/6250000000000 : ℝ)*(f.sum) + (598832479979/915000000000000000000000000 : ℝ)*base66 + (254057471256737537/91500000000000000000000000000000 : ℝ)*base67 + (453542148530262463/91500000000000000000000000000000 : ℝ)*base70 + (149109200138262463/91500000000000000000000000000000 : ℝ)*base72 + (391488469007/114375000000000000000000000 : ℝ)*base73 + (970116007556237537/91500000000000000000000000000000 : ℝ)*base75 + (219433909628262463/91500000000000000000000000000000 : ℝ)*base78 + (656939513510237537/91500000000000000000000000000000 : ℝ)*base79 + (75283061293/114375000000000000000000000 : ℝ)*base82 + (3899547/1250000000000000000000 : ℝ)*base90 + (3899547/1250000000000000000000 : ℝ)*base92 + (3899547/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1020256666109251976022435719/114375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1435714219/100000000000000 : ℝ)*(base19) + (106520121/25000000000000 : ℝ)*(base23) + (68902789/50000000000000 : ℝ)*(upper2) + (18040397/100000000000000 : ℝ)*(upper3) + (31153777/20000000000000 : ℝ)*(upper5) + (2929409846613667/50000000000000 : ℝ)*(major0) + (2929409846613667/50000000000000 : ℝ)*(major1) + (2929409846613667/50000000000000 : ℝ)*(major2) + (129890261/2000000000000 : ℝ)*(sp0) + (12142860121/20000000000000 : ℝ)*(sp1) + (7765539605736487/100000000000000 : ℝ)*(sp4) + (7765483950234713/100000000000000 : ℝ)*(sp5) + (7765545674169053/100000000000000 : ℝ)*(sp6) + (1976046494431281/50000000000000 : ℝ)*(sp7) + (1976046494431281/50000000000000 : ℝ)*(f.failure) + (7765546100249537/100000000000000 : ℝ)*(f.sum) + (151618588140353/6862500000000000000000000000 : ℝ)*base65 + (4016047928726489281/686250000000000000000000000000000 : ℝ)*base67 + (1921347339457260719/686250000000000000000000000000000 : ℝ)*base70 + (6134149776588989281/686250000000000000000000000000000 : ℝ)*base71 + (2111739457939/3431250000000000000000000000 : ℝ)*base73 + (2476546594616010719/686250000000000000000000000000000 : ℝ)*base76 + (4231120194652739281/686250000000000000000000000000000 : ℝ)*base77 + (3567533063568989281/686250000000000000000000000000000 : ℝ)*base79 + (113526575444431/13725000000000000000000000000 : ℝ)*base81 + (2868281/2500000000000000000000 : ℝ)*base90 + (2868281/2500000000000000000000 : ℝ)*base92 + (2868281/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1079_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1079_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1079_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1079_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
