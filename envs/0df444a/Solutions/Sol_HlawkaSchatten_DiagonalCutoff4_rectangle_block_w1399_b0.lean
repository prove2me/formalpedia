-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:45.368052+00:00
-- url     : https://prove2.me/submissions/679381a5-edc7-4cd6-9a0c-249aebdda3c3

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
theorem support_rectangle_w1399_s0_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355184949/2000000000 : ℝ)*x 0 + (238906391/400000000 : ℝ)*x 1 + (4824325271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355184949/2000000000 : ℝ)^4359 ≤ (5223156251973/50000000000000 : ℝ)^3335 := by
    have hnat : (355184949 : ℕ)^4359*50000000000000^3335 ≤ 5223156251973^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355184949 2000000000 5223156251973 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238906391/400000000 : ℝ)^4359 ≤ (50984818872809/100000000000000 : ℝ)^3335 := by
    have hnat : (238906391 : ℕ)^4359*100000000000000^3335 ≤ 50984818872809^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238906391 400000000 50984818872809 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824325271/10000000000 : ℝ)^4359 ≤ (602638571997/1562500000000 : ℝ)^3335 := by
    have hnat : (4824325271 : ℕ)^4359*1562500000000^3335 ≤ 602638571997^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824325271 10000000000 602638571997 1562500000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355184949/2000000000 : ℝ), (238906391/400000000 : ℝ), (4824325271/10000000000 : ℝ)] ![(5223156251973/50000000000000 : ℝ), (50984818872809/100000000000000 : ℝ), (602638571997/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355184949/2000000000 : ℝ)|^4359 ≤ (5223156251973/50000000000000 : ℝ)^3335
        have hw : |(-355184949/2000000000 : ℝ)|=(355184949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238906391/400000000 : ℝ)|^4359 ≤ (50984818872809/100000000000000 : ℝ)^3335
        have hw : |(238906391/400000000 : ℝ)|=(238906391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824325271/10000000000 : ℝ)|^4359 ≤ (602638571997/1562500000000 : ℝ)^3335
        have hw : |(4824325271/10000000000 : ℝ)|=(4824325271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (109908819/200000000 : ℝ)*x 0 + (-2425976291/10000000000 : ℝ)*x 1 + (4824325459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109908819/200000000 : ℝ)^4359 ≤ (714481962567/1562500000000 : ℝ)^3335 := by
    have hnat : (109908819 : ℕ)^4359*1562500000000^3335 ≤ 714481962567^3335*200000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109908819 200000000 714481962567 1562500000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2425976291/10000000000 : ℝ)^4359 ≤ (15704283808387/100000000000000 : ℝ)^3335 := by
    have hnat : (2425976291 : ℕ)^4359*100000000000000^3335 ≤ 15704283808387^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425976291 10000000000 15704283808387 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824325459/10000000000 : ℝ)^4359 ≤ (7713774114459/20000000000000 : ℝ)^3335 := by
    have hnat : (4824325459 : ℕ)^4359*20000000000000^3335 ≤ 7713774114459^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824325459 10000000000 7713774114459 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109908819/200000000 : ℝ), (-2425976291/10000000000 : ℝ), (4824325459/10000000000 : ℝ)] ![(714481962567/1562500000000 : ℝ), (15704283808387/100000000000000 : ℝ), (7713774114459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109908819/200000000 : ℝ)|^4359 ≤ (714481962567/1562500000000 : ℝ)^3335
        have hw : |(109908819/200000000 : ℝ)|=(109908819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2425976291/10000000000 : ℝ)|^4359 ≤ (15704283808387/100000000000000 : ℝ)^3335
        have hw : |(-2425976291/10000000000 : ℝ)|=(2425976291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824325459/10000000000 : ℝ)|^4359 ≤ (7713774114459/20000000000000 : ℝ)^3335
        have hw : |(4824325459/10000000000 : ℝ)|=(4824325459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5495440961/10000000000 : ℝ)*x 0 + (4824325431/10000000000 : ℝ)*x 1 + (-2425976311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495440961/10000000000 : ℝ)^4359 ≤ (45726845723921/100000000000000 : ℝ)^3335 := by
    have hnat : (5495440961 : ℕ)^4359*100000000000000^3335 ≤ 45726845723921^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495440961 10000000000 45726845723921 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824325431/10000000000 : ℝ)^4359 ≤ (1205277196241/3125000000000 : ℝ)^3335 := by
    have hnat : (4824325431 : ℕ)^4359*3125000000000^3335 ≤ 1205277196241^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824325431 10000000000 1205277196241 3125000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2425976311/10000000000 : ℝ)^4359 ≤ (15704283977607/100000000000000 : ℝ)^3335 := by
    have hnat : (2425976311 : ℕ)^4359*100000000000000^3335 ≤ 15704283977607^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425976311 10000000000 15704283977607 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495440961/10000000000 : ℝ), (4824325431/10000000000 : ℝ), (-2425976311/10000000000 : ℝ)] ![(45726845723921/100000000000000 : ℝ), (1205277196241/3125000000000 : ℝ), (15704283977607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495440961/10000000000 : ℝ)|^4359 ≤ (45726845723921/100000000000000 : ℝ)^3335
        have hw : |(5495440961/10000000000 : ℝ)|=(5495440961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824325431/10000000000 : ℝ)|^4359 ≤ (1205277196241/3125000000000 : ℝ)^3335
        have hw : |(4824325431/10000000000 : ℝ)|=(4824325431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2425976311/10000000000 : ℝ)|^4359 ≤ (15704283977607/100000000000000 : ℝ)^3335
        have hw : |(-2425976311/10000000000 : ℝ)|=(2425976311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170334893/10000000000 : ℝ)*x 0 + (1552109899/5000000000 : ℝ)*x 1 + (1390292949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170334893/10000000000 : ℝ)^4359 ≤ (7970503618883/25000000000000 : ℝ)^3335 := by
    have hnat : (4170334893 : ℕ)^4359*25000000000000^3335 ≤ 7970503618883^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170334893 10000000000 7970503618883 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552109899/5000000000 : ℝ)^4359 ≤ (21674957699511/100000000000000 : ℝ)^3335 := by
    have hnat : (1552109899 : ℕ)^4359*100000000000000^3335 ≤ 21674957699511^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552109899 5000000000 21674957699511 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390292949/2500000000 : ℝ)^4359 ≤ (46443027800631/100000000000000 : ℝ)^3335 := by
    have hnat : (1390292949 : ℕ)^4359*100000000000000^3335 ≤ 46443027800631^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390292949 2500000000 46443027800631 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170334893/10000000000 : ℝ), (1552109899/5000000000 : ℝ), (1390292949/2500000000 : ℝ)] ![(7970503618883/25000000000000 : ℝ), (21674957699511/100000000000000 : ℝ), (46443027800631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170334893/10000000000 : ℝ)|^4359 ≤ (7970503618883/25000000000000 : ℝ)^3335
        have hw : |(4170334893/10000000000 : ℝ)|=(4170334893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552109899/5000000000 : ℝ)|^4359 ≤ (21674957699511/100000000000000 : ℝ)^3335
        have hw : |(1552109899/5000000000 : ℝ)|=(1552109899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1390292949/2500000000 : ℝ)|^4359 ≤ (46443027800631/100000000000000 : ℝ)^3335
        have hw : |(1390292949/2500000000 : ℝ)|=(1390292949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356018007/2000000000 : ℝ)*x 0 + (970754271/2000000000 : ℝ)*x 1 + (5942161319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356018007/2000000000 : ℝ)^4359 ≤ (10478347966281/100000000000000 : ℝ)^3335 := by
    have hnat : (356018007 : ℕ)^4359*100000000000000^3335 ≤ 10478347966281^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356018007 2000000000 10478347966281 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970754271/2000000000 : ℝ)^4359 ≤ (19438425217297/50000000000000 : ℝ)^3335 := by
    have hnat : (970754271 : ℕ)^4359*50000000000000^3335 ≤ 19438425217297^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970754271 2000000000 19438425217297 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5942161319/10000000000 : ℝ)^4359 ≤ (25322400795771/50000000000000 : ℝ)^3335 := by
    have hnat : (5942161319 : ℕ)^4359*50000000000000^3335 ≤ 25322400795771^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942161319 10000000000 25322400795771 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356018007/2000000000 : ℝ), (970754271/2000000000 : ℝ), (5942161319/10000000000 : ℝ)] ![(10478347966281/100000000000000 : ℝ), (19438425217297/50000000000000 : ℝ), (25322400795771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356018007/2000000000 : ℝ)|^4359 ≤ (10478347966281/100000000000000 : ℝ)^3335
        have hw : |(-356018007/2000000000 : ℝ)|=(356018007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970754271/2000000000 : ℝ)|^4359 ≤ (19438425217297/50000000000000 : ℝ)^3335
        have hw : |(970754271/2000000000 : ℝ)|=(970754271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5942161319/10000000000 : ℝ)|^4359 ≤ (25322400795771/50000000000000 : ℝ)^3335
        have hw : |(5942161319/10000000000 : ℝ)|=(5942161319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036432583/2000000000 : ℝ)*x 0 + (-261627843/2000000000 : ℝ)*x 1 + (5942160083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036432583/2000000000 : ℝ)^4359 ≤ (4234992928693/10000000000000 : ℝ)^3335 := by
    have hnat : (1036432583 : ℕ)^4359*10000000000000^3335 ≤ 4234992928693^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036432583 2000000000 4234992928693 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261627843/2000000000 : ℝ)^4359 ≤ (875660359993/12500000000000 : ℝ)^3335 := by
    have hnat : (261627843 : ℕ)^4359*12500000000000^3335 ≤ 875660359993^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261627843 2000000000 875660359993 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5942160083/10000000000 : ℝ)^4359 ≤ (2532239391131/5000000000000 : ℝ)^3335 := by
    have hnat : (5942160083 : ℕ)^4359*5000000000000^3335 ≤ 2532239391131^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942160083 10000000000 2532239391131 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036432583/2000000000 : ℝ), (-261627843/2000000000 : ℝ), (5942160083/10000000000 : ℝ)] ![(4234992928693/10000000000000 : ℝ), (875660359993/12500000000000 : ℝ), (2532239391131/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036432583/2000000000 : ℝ)|^4359 ≤ (4234992928693/10000000000000 : ℝ)^3335
        have hw : |(1036432583/2000000000 : ℝ)|=(1036432583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261627843/2000000000 : ℝ)|^4359 ≤ (875660359993/12500000000000 : ℝ)^3335
        have hw : |(-261627843/2000000000 : ℝ)|=(261627843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5942160083/10000000000 : ℝ)|^4359 ≤ (2532239391131/5000000000000 : ℝ)^3335
        have hw : |(5942160083/10000000000 : ℝ)|=(5942160083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5182159123/10000000000 : ℝ)*x 0 + (5942163831/10000000000 : ℝ)*x 1 + (-327034759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182159123/10000000000 : ℝ)^4359 ≤ (5293736097831/12500000000000 : ℝ)^3335 := by
    have hnat : (5182159123 : ℕ)^4359*12500000000000^3335 ≤ 5293736097831^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182159123 10000000000 5293736097831 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5942163831/10000000000 : ℝ)^4359 ≤ (6330603696873/12500000000000 : ℝ)^3335 := by
    have hnat : (5942163831 : ℕ)^4359*12500000000000^3335 ≤ 6330603696873^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942163831 10000000000 6330603696873 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327034759/2500000000 : ℝ)^4359 ≤ (3502640813523/50000000000000 : ℝ)^3335 := by
    have hnat : (327034759 : ℕ)^4359*50000000000000^3335 ≤ 3502640813523^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327034759 2500000000 3502640813523 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182159123/10000000000 : ℝ), (5942163831/10000000000 : ℝ), (-327034759/2500000000 : ℝ)] ![(5293736097831/12500000000000 : ℝ), (6330603696873/12500000000000 : ℝ), (3502640813523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182159123/10000000000 : ℝ)|^4359 ≤ (5293736097831/12500000000000 : ℝ)^3335
        have hw : |(5182159123/10000000000 : ℝ)|=(5182159123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5942163831/10000000000 : ℝ)|^4359 ≤ (6330603696873/12500000000000 : ℝ)^3335
        have hw : |(5942163831/10000000000 : ℝ)|=(5942163831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-327034759/2500000000 : ℝ)|^4359 ≤ (3502640813523/50000000000000 : ℝ)^3335
        have hw : |(-327034759/2500000000 : ℝ)|=(327034759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s0_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179242221/10000000000 : ℝ)*x 0 + (5498170331/10000000000 : ℝ)*x 1 + (633895169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179242221/10000000000 : ℝ)^4359 ≤ (15985524209881/50000000000000 : ℝ)^3335 := by
    have hnat : (4179242221 : ℕ)^4359*50000000000000^3335 ≤ 15985524209881^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179242221 10000000000 15985524209881 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498170331/10000000000 : ℝ)^4359 ≤ (45756531967859/100000000000000 : ℝ)^3335 := by
    have hnat : (5498170331 : ℕ)^4359*100000000000000^3335 ≤ 45756531967859^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498170331 10000000000 45756531967859 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633895169/2000000000 : ℝ)^4359 ≤ (11136209798923/50000000000000 : ℝ)^3335 := by
    have hnat : (633895169 : ℕ)^4359*50000000000000^3335 ≤ 11136209798923^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633895169 2000000000 11136209798923 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179242221/10000000000 : ℝ), (5498170331/10000000000 : ℝ), (633895169/2000000000 : ℝ)] ![(15985524209881/50000000000000 : ℝ), (45756531967859/100000000000000 : ℝ), (11136209798923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179242221/10000000000 : ℝ)|^4359 ≤ (15985524209881/50000000000000 : ℝ)^3335
        have hw : |(4179242221/10000000000 : ℝ)|=(4179242221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498170331/10000000000 : ℝ)|^4359 ≤ (45756531967859/100000000000000 : ℝ)^3335
        have hw : |(5498170331/10000000000 : ℝ)|=(5498170331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633895169/2000000000 : ℝ)|^4359 ≤ (11136209798923/50000000000000 : ℝ)^3335
        have hw : |(633895169/2000000000 : ℝ)|=(633895169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (917/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26467/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2179/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2179 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2179*1^512 ≤ 0^512*1^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2179/512 : ℝ) ≤ (404998373505994711/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2179 ≤ (404998373505994711/20000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2179*20000000000000000000^512 ≤ 404998373505994711^512*5^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 404998373505994711 20000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (404998373505994711/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2179 := by
      have hnat : (1 : ℕ)^512*1^2179 ≤ 1^2179*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20404998373505994711/20000000000000000000 : ℝ) ≤ (10047217039184927/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (20404998373505994711/20000000000000000000 : ℝ)^512 ≤ (10047217039184927/10000000000000000 : ℝ)^2179 := by
      have hnat : (20404998373505994711 : ℕ)^512*10000000000000000^2179 ≤ 10047217039184927^2179*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20404998373505994711 20000000000000000000 10047217039184927 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047217039184927/10000000000000000 : ℝ)) (X := (20404998373505994711/20000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10404998373505994711/10000000000000000000 : ℝ) ≤ (5047217039184927/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (10404998373505994711/10000000000000000000 : ℝ)^512 ≤ (5047217039184927/5000000000000000 : ℝ)^2179 := by
      have hnat : (10404998373505994711 : ℕ)^512*5000000000000000^2179 ≤ 5047217039184927^2179*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10404998373505994711 10000000000000000000 5047217039184927 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047217039184927/5000000000000000 : ℝ)) (X := (10404998373505994711/10000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47217039184927/4000000000000000 : ℝ)*(0 : ℝ))^(2179/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(47217039184927/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(404998373505994711/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47217039184927/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (1 : ℝ)+(47217039184927/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047217039184927/10000000000000000 : ℝ) by norm_num, show 1+(404998373505994711/20000000000000000000 : ℝ)+(0 : ℝ)=(20404998373505994711/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(404998373505994711/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47217039184927/4000000000000000 : ℝ)*(2/5 : ℝ))^(2179/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(47217039184927/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047217039184927/5000000000000000 : ℝ) by norm_num, show 1+2*(404998373505994711/20000000000000000000 : ℝ)=(10404998373505994711/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47217039184927/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47217039184927/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47217039184927/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47217039184927/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47217039184927/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47217039184927/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-355184949/2000000000 : ℝ)*X 0 0+(238906391/400000000 : ℝ)*X 0 1+(4824325271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((109908819/200000000 : ℝ)*X 1 0+(-2425976291/10000000000 : ℝ)*X 1 1+(4824325459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5495440961/10000000000 : ℝ)*X 2 0+(4824325431/10000000000 : ℝ)*X 2 1+(-2425976311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4170334893/10000000000 : ℝ)*X 0 0+(1552109899/5000000000 : ℝ)*X 0 1+(1390292949/2500000000 : ℝ)*X 0 2+(4170334893/10000000000 : ℝ)*X 1 0+(1552109899/5000000000 : ℝ)*X 1 1+(1390292949/2500000000 : ℝ)*X 1 2+(4170334893/10000000000 : ℝ)*X 2 0+(1552109899/5000000000 : ℝ)*X 2 1+(1390292949/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-356018007/2000000000 : ℝ)*X 0 0+(970754271/2000000000 : ℝ)*X 0 1+(5942161319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036432583/2000000000 : ℝ)*X 1 0+(-261627843/2000000000 : ℝ)*X 1 1+(5942160083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182159123/10000000000 : ℝ)*X 2 0+(5942163831/10000000000 : ℝ)*X 2 1+(-327034759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4179242221/10000000000 : ℝ)*X 0 0+(5498170331/10000000000 : ℝ)*X 0 1+(633895169/2000000000 : ℝ)*X 0 2+(4179242221/10000000000 : ℝ)*X 1 0+(5498170331/10000000000 : ℝ)*X 1 1+(633895169/2000000000 : ℝ)*X 1 2+(4179242221/10000000000 : ℝ)*X 2 0+(5498170331/10000000000 : ℝ)*X 2 1+(633895169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209485860967263684902577/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216289/50000000000000 : ℝ)*(base1) + (489064059/100000000000000 : ℝ)*(base19) + (490807163/100000000000000 : ℝ)*(base23) + (67074531/100000000000000 : ℝ)*(upper3) + (62316307/100000000000000 : ℝ)*(upper5) + (638919998322683/100000000000000 : ℝ)*(major0) + (638919998322683/100000000000000 : ℝ)*(major1) + (638919998322683/100000000000000 : ℝ)*(major2) + (870828132566251/100000000000000 : ℝ)*(sp0) + (21770736034941/2500000000000 : ℝ)*(sp1) + (108853679956817/12500000000000 : ℝ)*(sp2) + (81401829437753/20000000000000 : ℝ)*(sp3) + (72013121/4000000000000 : ℝ)*(sp4) + (423366849/50000000000000 : ℝ)*(sp7) + (203504998177521/50000000000000 : ℝ)*(f.failure) + (435414965230849/50000000000000 : ℝ)*(f.sum) + (91199749199141/200000000000000000000000000000 : ℝ)*base65 + (1545661092599141/400000000000000000000000000000 : ℝ)*base67 + (2811409157399141/400000000000000000000000000000 : ℝ)*base69 + (1115726094599141/400000000000000000000000000000 : ℝ)*base71 + (66540597800859/200000000000000000000000000000 : ℝ)*base74 + (687319948200859/400000000000000000000000000000 : ℝ)*base76 + (1621929656199141/400000000000000000000000000000 : ℝ)*base77 + (718469953800859/400000000000000000000000000000 : ℝ)*base80 + (175345444999141/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3859069/1000000000000000000000 : ℝ)*base89 + (3859069/1000000000000000000000 : ℝ)*base91 + (3859069/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (465755347750814597424759/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473418961/25000000000000 : ℝ)*(base19) + (459121259/25000000000000 : ℝ)*(base23) + (8154459/1250000000000 : ℝ)*(base39) + (395703/1250000000000 : ℝ)*(upper2) + (447291891/100000000000000 : ℝ)*(upper5) + (674104542654841/100000000000000 : ℝ)*(major0) + (674104542654841/100000000000000 : ℝ)*(major1) + (674103890298121/100000000000000 : ℝ)*(major2) + (732288071/12500000000000 : ℝ)*(sp1) + (4477621167/100000000000000 : ℝ)*(sp2) + (459392291230687/50000000000000 : ℝ)*(sp4) + (918776830480963/100000000000000 : ℝ)*(sp5) + (918778920711891/100000000000000 : ℝ)*(sp6) + (26838971249251/6250000000000 : ℝ)*(sp7) + (26838971249251/6250000000000 : ℝ)*(f.failure) + (183757046963619/20000000000000 : ℝ)*(f.sum) + (382117016001887/200000000000000000000000000000 : ℝ)*base65 + (438246853222167/400000000000000000000000000000 : ℝ)*base67 + (243449000381607/400000000000000000000000000000 : ℝ)*base69 + (662023232777833/400000000000000000000000000000 : ℝ)*base72 + (670301712601887/200000000000000000000000000000 : ℝ)*base73 + (2802152733618393/400000000000000000000000000000 : ℝ)*base76 + (172244684381607/400000000000000000000000000000 : ℝ)*base77 + (1529569053181607/400000000000000000000000000000 : ℝ)*base79 + (121631029381607/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (445961/125000000000000000000 : ℝ)*base90 + (445961/125000000000000000000 : ℝ)*base92 + (445961/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (917/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26467/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_s1_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-195254727/1000000000 : ℝ)*x 0 + (2808744803/5000000000 : ℝ)*x 1 + (5066314873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195254727/1000000000 : ℝ)^4359 ≤ (2956128256529/25000000000000 : ℝ)^3335 := by
    have hnat : (195254727 : ℕ)^4359*25000000000000^3335 ≤ 2956128256529^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195254727 1000000000 2956128256529 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808744803/5000000000 : ℝ)^4359 ≤ (9411744131979/20000000000000 : ℝ)^3335 := by
    have hnat : (2808744803 : ℕ)^4359*20000000000000^3335 ≤ 9411744131979^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808744803 5000000000 9411744131979 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5066314873/10000000000 : ℝ)^4359 ≤ (8223353259753/20000000000000 : ℝ)^3335 := by
    have hnat : (5066314873 : ℕ)^4359*20000000000000^3335 ≤ 8223353259753^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066314873 10000000000 8223353259753 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195254727/1000000000 : ℝ), (2808744803/5000000000 : ℝ), (5066314873/10000000000 : ℝ)] ![(2956128256529/25000000000000 : ℝ), (9411744131979/20000000000000 : ℝ), (8223353259753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195254727/1000000000 : ℝ)|^4359 ≤ (2956128256529/25000000000000 : ℝ)^3335
        have hw : |(-195254727/1000000000 : ℝ)|=(195254727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808744803/5000000000 : ℝ)|^4359 ≤ (9411744131979/20000000000000 : ℝ)^3335
        have hw : |(2808744803/5000000000 : ℝ)|=(2808744803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5066314873/10000000000 : ℝ)|^4359 ≤ (8223353259753/20000000000000 : ℝ)^3335
        have hw : |(5066314873/10000000000 : ℝ)|=(5066314873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399843841/10000000000 : ℝ)*x 0 + (-2245289047/10000000000 : ℝ)*x 1 + (5066316221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399843841/10000000000 : ℝ)^4359 ≤ (44689942007043/100000000000000 : ℝ)^3335 := by
    have hnat : (5399843841 : ℕ)^4359*100000000000000^3335 ≤ 44689942007043^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399843841 10000000000 44689942007043 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245289047/10000000000 : ℝ)^4359 ≤ (7096638687811/50000000000000 : ℝ)^3335 := by
    have hnat : (2245289047 : ℕ)^4359*50000000000000^3335 ≤ 7096638687811^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245289047 10000000000 7096638687811 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5066316221/10000000000 : ℝ)^4359 ≤ (5139597574729/12500000000000 : ℝ)^3335 := by
    have hnat : (5066316221 : ℕ)^4359*12500000000000^3335 ≤ 5139597574729^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066316221 10000000000 5139597574729 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399843841/10000000000 : ℝ), (-2245289047/10000000000 : ℝ), (5066316221/10000000000 : ℝ)] ![(44689942007043/100000000000000 : ℝ), (7096638687811/50000000000000 : ℝ), (5139597574729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399843841/10000000000 : ℝ)|^4359 ≤ (44689942007043/100000000000000 : ℝ)^3335
        have hw : |(5399843841/10000000000 : ℝ)|=(5399843841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245289047/10000000000 : ℝ)|^4359 ≤ (7096638687811/50000000000000 : ℝ)^3335
        have hw : |(-2245289047/10000000000 : ℝ)|=(2245289047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5066316221/10000000000 : ℝ)|^4359 ≤ (5139597574729/12500000000000 : ℝ)^3335
        have hw : |(5066316221/10000000000 : ℝ)|=(5066316221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079968953/2000000000 : ℝ)*x 0 + (5066315057/10000000000 : ℝ)*x 1 + (-2245289333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079968953/2000000000 : ℝ)^4359 ≤ (22344976001123/50000000000000 : ℝ)^3335 := by
    have hnat : (1079968953 : ℕ)^4359*50000000000000^3335 ≤ 22344976001123^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079968953 2000000000 22344976001123 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5066315057/10000000000 : ℝ)^4359 ≤ (20558384125283/50000000000000 : ℝ)^3335 := by
    have hnat : (5066315057 : ℕ)^4359*50000000000000^3335 ≤ 20558384125283^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066315057 10000000000 20558384125283 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245289333/10000000000 : ℝ)^4359 ≤ (7096639869321/50000000000000 : ℝ)^3335 := by
    have hnat : (2245289333 : ℕ)^4359*50000000000000^3335 ≤ 7096639869321^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245289333 10000000000 7096639869321 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079968953/2000000000 : ℝ), (5066315057/10000000000 : ℝ), (-2245289333/10000000000 : ℝ)] ![(22344976001123/50000000000000 : ℝ), (20558384125283/50000000000000 : ℝ), (7096639869321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079968953/2000000000 : ℝ)|^4359 ≤ (22344976001123/50000000000000 : ℝ)^3335
        have hw : |(1079968953/2000000000 : ℝ)|=(1079968953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5066315057/10000000000 : ℝ)|^4359 ≤ (20558384125283/50000000000000 : ℝ)^3335
        have hw : |(5066315057/10000000000 : ℝ)|=(5066315057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245289333/10000000000 : ℝ)|^4359 ≤ (7096639869321/50000000000000 : ℝ)^3335
        have hw : |(-2245289333/10000000000 : ℝ)|=(2245289333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282075177/10000000000 : ℝ)*x 0 + (3729142441/10000000000 : ℝ)*x 1 + (2454210427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282075177/10000000000 : ℝ)^4359 ≤ (33003122724883/100000000000000 : ℝ)^3335 := by
    have hnat : (4282075177 : ℕ)^4359*100000000000000^3335 ≤ 33003122724883^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282075177 10000000000 33003122724883 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3729142441/10000000000 : ℝ)^4359 ≤ (13773459010551/50000000000000 : ℝ)^3335 := by
    have hnat : (3729142441 : ℕ)^4359*50000000000000^3335 ≤ 13773459010551^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729142441 10000000000 13773459010551 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454210427/5000000000 : ℝ)^4359 ≤ (39449959245659/100000000000000 : ℝ)^3335 := by
    have hnat : (2454210427 : ℕ)^4359*100000000000000^3335 ≤ 39449959245659^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454210427 5000000000 39449959245659 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282075177/10000000000 : ℝ), (3729142441/10000000000 : ℝ), (2454210427/5000000000 : ℝ)] ![(33003122724883/100000000000000 : ℝ), (13773459010551/50000000000000 : ℝ), (39449959245659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282075177/10000000000 : ℝ)|^4359 ≤ (33003122724883/100000000000000 : ℝ)^3335
        have hw : |(4282075177/10000000000 : ℝ)|=(4282075177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3729142441/10000000000 : ℝ)|^4359 ≤ (13773459010551/50000000000000 : ℝ)^3335
        have hw : |(3729142441/10000000000 : ℝ)|=(3729142441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454210427/5000000000 : ℝ)|^4359 ≤ (39449959245659/100000000000000 : ℝ)^3335
        have hw : |(2454210427/5000000000 : ℝ)|=(2454210427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-195298859/1000000000 : ℝ)*x 0 + (126823303/250000000 : ℝ)*x 1 + (1402689331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195298859/1000000000 : ℝ)^4359 ≤ (5914003185309/50000000000000 : ℝ)^3335 := by
    have hnat : (195298859 : ℕ)^4359*50000000000000^3335 ≤ 5914003185309^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195298859 1000000000 5914003185309 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126823303/250000000 : ℝ)^4359 ≤ (8237394717449/20000000000000 : ℝ)^3335 := by
    have hnat : (126823303 : ℕ)^4359*20000000000000^3335 ≤ 8237394717449^3335*250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126823303 250000000 8237394717449 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1402689331/2500000000 : ℝ)^4359 ≤ (46985020024259/100000000000000 : ℝ)^3335 := by
    have hnat : (1402689331 : ℕ)^4359*100000000000000^3335 ≤ 46985020024259^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402689331 2500000000 46985020024259 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195298859/1000000000 : ℝ), (126823303/250000000 : ℝ), (1402689331/2500000000 : ℝ)] ![(5914003185309/50000000000000 : ℝ), (8237394717449/20000000000000 : ℝ), (46985020024259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195298859/1000000000 : ℝ)|^4359 ≤ (5914003185309/50000000000000 : ℝ)^3335
        have hw : |(-195298859/1000000000 : ℝ)|=(195298859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126823303/250000000 : ℝ)|^4359 ≤ (8237394717449/20000000000000 : ℝ)^3335
        have hw : |(126823303/250000000 : ℝ)|=(126823303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1402689331/2500000000 : ℝ)|^4359 ≤ (46985020024259/100000000000000 : ℝ)^3335
        have hw : |(1402689331/2500000000 : ℝ)|=(1402689331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628081857/5000000000 : ℝ)*x 0 + (-1700847893/10000000000 : ℝ)*x 1 + (5610757277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628081857/5000000000 : ℝ)^4359 ≤ (43142096772517/100000000000000 : ℝ)^3335 := by
    have hnat : (2628081857 : ℕ)^4359*100000000000000^3335 ≤ 43142096772517^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628081857 5000000000 43142096772517 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1700847893/10000000000 : ℝ)^4359 ≤ (9872883705531/100000000000000 : ℝ)^3335 := by
    have hnat : (1700847893 : ℕ)^4359*100000000000000^3335 ≤ 9872883705531^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700847893 10000000000 9872883705531 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5610757277/10000000000 : ℝ)^4359 ≤ (11746254877457/25000000000000 : ℝ)^3335 := by
    have hnat : (5610757277 : ℕ)^4359*25000000000000^3335 ≤ 11746254877457^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610757277 10000000000 11746254877457 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628081857/5000000000 : ℝ), (-1700847893/10000000000 : ℝ), (5610757277/10000000000 : ℝ)] ![(43142096772517/100000000000000 : ℝ), (9872883705531/100000000000000 : ℝ), (11746254877457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628081857/5000000000 : ℝ)|^4359 ≤ (43142096772517/100000000000000 : ℝ)^3335
        have hw : |(2628081857/5000000000 : ℝ)|=(2628081857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1700847893/10000000000 : ℝ)|^4359 ≤ (9872883705531/100000000000000 : ℝ)^3335
        have hw : |(-1700847893/10000000000 : ℝ)|=(1700847893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5610757277/10000000000 : ℝ)|^4359 ≤ (11746254877457/25000000000000 : ℝ)^3335
        have hw : |(5610757277/10000000000 : ℝ)|=(5610757277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256164229/10000000000 : ℝ)*x 0 + (5610757703/10000000000 : ℝ)*x 1 + (-1700846551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256164229/10000000000 : ℝ)^4359 ≤ (5392762787187/12500000000000 : ℝ)^3335 := by
    have hnat : (5256164229 : ℕ)^4359*12500000000000^3335 ≤ 5392762787187^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256164229 10000000000 5392762787187 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5610757703/10000000000 : ℝ)^4359 ≤ (2349251208627/5000000000000 : ℝ)^3335 := by
    have hnat : (5610757703 : ℕ)^4359*5000000000000^3335 ≤ 2349251208627^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610757703 10000000000 2349251208627 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1700846551/10000000000 : ℝ)^4359 ≤ (987287352379/10000000000000 : ℝ)^3335 := by
    have hnat : (1700846551 : ℕ)^4359*10000000000000^3335 ≤ 987287352379^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700846551 10000000000 987287352379 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256164229/10000000000 : ℝ), (5610757703/10000000000 : ℝ), (-1700846551/10000000000 : ℝ)] ![(5392762787187/12500000000000 : ℝ), (2349251208627/5000000000000 : ℝ), (987287352379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256164229/10000000000 : ℝ)|^4359 ≤ (5392762787187/12500000000000 : ℝ)^3335
        have hw : |(5256164229/10000000000 : ℝ)|=(5256164229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5610757703/10000000000 : ℝ)|^4359 ≤ (2349251208627/5000000000000 : ℝ)^3335
        have hw : |(5610757703/10000000000 : ℝ)|=(5610757703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1700846551/10000000000 : ℝ)|^4359 ≤ (987287352379/10000000000000 : ℝ)^3335
        have hw : |(-1700846551/10000000000 : ℝ)|=(1700846551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s1_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141510501/5000000000 : ℝ)*x 0 + (2447131367/5000000000 : ℝ)*x 1 + (1871772331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141510501/5000000000 : ℝ)^4359 ≤ (33012651065913/100000000000000 : ℝ)^3335 := by
    have hnat : (2141510501 : ℕ)^4359*100000000000000^3335 ≤ 33012651065913^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141510501 5000000000 33012651065913 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2447131367/5000000000 : ℝ)^4359 ≤ (39301294190591/100000000000000 : ℝ)^3335 := by
    have hnat : (2447131367 : ℕ)^4359*100000000000000^3335 ≤ 39301294190591^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447131367 5000000000 39301294190591 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871772331/5000000000 : ℝ)^4359 ≤ (27686054734773/100000000000000 : ℝ)^3335 := by
    have hnat : (1871772331 : ℕ)^4359*100000000000000^3335 ≤ 27686054734773^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871772331 5000000000 27686054734773 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141510501/5000000000 : ℝ), (2447131367/5000000000 : ℝ), (1871772331/5000000000 : ℝ)] ![(33012651065913/100000000000000 : ℝ), (39301294190591/100000000000000 : ℝ), (27686054734773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141510501/5000000000 : ℝ)|^4359 ≤ (33012651065913/100000000000000 : ℝ)^3335
        have hw : |(2141510501/5000000000 : ℝ)|=(2141510501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2447131367/5000000000 : ℝ)|^4359 ≤ (39301294190591/100000000000000 : ℝ)^3335
        have hw : |(2447131367/5000000000 : ℝ)|=(2447131367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1871772331/5000000000 : ℝ)|^4359 ≤ (27686054734773/100000000000000 : ℝ)^3335
        have hw : |(1871772331/5000000000 : ℝ)|=(1871772331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (917/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (381/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26467/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (917/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26467/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (917/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26467/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (917/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26467/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (917/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26467/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (917/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26467/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (917/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (917/50000 : ℝ) ^ (2179/512 : ℝ) ≤ (1016744360697/25000000000000000000 : ℝ) := by
    have hpowers : (917/50000 : ℝ)^2179 ≤ (1016744360697/25000000000000000000 : ℝ)^512 := by
      have hnat : (917 : ℕ)^2179*25000000000000000000^512 ≤ 1016744360697^512*50000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        917 50000 1016744360697 25000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (917/50000 : ℝ)) (X := (1016744360697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26467/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (21826921003991509/6250000000000000000 : ℝ) := by
    have hpowers : (26467/100000 : ℝ)^2179 ≤ (21826921003991509/6250000000000000000 : ℝ)^512 := by
      have hnat : (26467 : ℕ)^2179*6250000000000000000^512 ≤ 21826921003991509^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26467 100000 21826921003991509 6250000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26467/100000 : ℝ)) (X := (21826921003991509/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500001016744360697/12500000000000000000 : ℝ) ≤ (10000000191123671/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (12500001016744360697/12500000000000000000 : ℝ)^512 ≤ (10000000191123671/10000000000000000 : ℝ)^2179 := by
      have hnat : (12500001016744360697 : ℕ)^512*10000000000000000^2179 ≤ 10000000191123671^2179*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500001016744360697 12500000000000000000 10000000191123671 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000191123671/10000000000000000 : ℝ)) (X := (12500001016744360697/12500000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25087308700760326733/25000000000000000000 : ℝ) ≤ (10008195036406829/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (25087308700760326733/25000000000000000000 : ℝ)^512 ≤ (10008195036406829/10000000000000000 : ℝ)^2179 := by
      have hnat : (25087308700760326733 : ℕ)^512*10000000000000000^2179 ≤ 10008195036406829^2179*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25087308700760326733 25000000000000000000 10008195036406829 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008195036406829/10000000000000000 : ℝ)) (X := (25087308700760326733/25000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3146826921003991509/3125000000000000000 : ℝ) ≤ (10016389881689987/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (3146826921003991509/3125000000000000000 : ℝ)^512 ≤ (10016389881689987/10000000000000000 : ℝ)^2179 := by
      have hnat : (3146826921003991509 : ℕ)^512*10000000000000000^2179 ≤ 10016389881689987^2179*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3146826921003991509 3125000000000000000 10016389881689987 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016389881689987/10000000000000000 : ℝ)) (X := (3146826921003991509/3125000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1016744360697/25000000000000000000 : ℝ) ≤ ((11728568857878607819/11730000000000000000 : ℝ)+2*(1365807547193/410550000000000 : ℝ)*(917/50000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (11728568857878607819/11730000000000000000 : ℝ)+2*(1365807547193/410550000000000 : ℝ)*(917/50000 : ℝ)=(10000000191123671/10000000000000000 : ℝ) by norm_num, show 1+2*(1016744360697/25000000000000000000 : ℝ)=(12500001016744360697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21826921003991509/6250000000000000000 : ℝ)+(1016744360697/25000000000000000000 : ℝ) ≤ ((11728568857878607819/11730000000000000000 : ℝ)+(1365807547193/410550000000000 : ℝ)*((26467/100000 : ℝ)+(917/50000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (11728568857878607819/11730000000000000000 : ℝ)+(1365807547193/410550000000000 : ℝ)*((26467/100000 : ℝ)+(917/50000 : ℝ))=(10008195036406829/10000000000000000 : ℝ) by norm_num, show 1+(21826921003991509/6250000000000000000 : ℝ)+(1016744360697/25000000000000000000 : ℝ)=(25087308700760326733/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21826921003991509/6250000000000000000 : ℝ) ≤ ((11728568857878607819/11730000000000000000 : ℝ)+2*(1365807547193/410550000000000 : ℝ)*(26467/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (11728568857878607819/11730000000000000000 : ℝ)+2*(1365807547193/410550000000000 : ℝ)*(26467/100000 : ℝ)=(10016389881689987/10000000000000000 : ℝ) by norm_num, show 1+2*(21826921003991509/6250000000000000000 : ℝ)=(3146826921003991509/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11728568857878607819/11730000000000000000 : ℝ)*(X 1 0+X 2 0)+(1365807547193/410550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (917/50000 : ℝ)) (hi := (26467/100000 : ℝ)) (c := (11728568857878607819/11730000000000000000 : ℝ)) (alpha := (1365807547193/410550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11728568857878607819/11730000000000000000 : ℝ)*(X 0 1+X 2 1)+(1365807547193/410550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (917/50000 : ℝ)) (hi := (26467/100000 : ℝ)) (c := (11728568857878607819/11730000000000000000 : ℝ)) (alpha := (1365807547193/410550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11728568857878607819/11730000000000000000 : ℝ)*(X 0 2+X 1 2)+(1365807547193/410550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (917/50000 : ℝ)) (hi := (26467/100000 : ℝ)) (c := (11728568857878607819/11730000000000000000 : ℝ)) (alpha := (1365807547193/410550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-195254727/1000000000 : ℝ)*X 0 0+(2808744803/5000000000 : ℝ)*X 0 1+(5066314873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5399843841/10000000000 : ℝ)*X 1 0+(-2245289047/10000000000 : ℝ)*X 1 1+(5066316221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1079968953/2000000000 : ℝ)*X 2 0+(5066315057/10000000000 : ℝ)*X 2 1+(-2245289333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282075177/10000000000 : ℝ)*X 0 0+(3729142441/10000000000 : ℝ)*X 0 1+(2454210427/5000000000 : ℝ)*X 0 2+(4282075177/10000000000 : ℝ)*X 1 0+(3729142441/10000000000 : ℝ)*X 1 1+(2454210427/5000000000 : ℝ)*X 1 2+(4282075177/10000000000 : ℝ)*X 2 0+(3729142441/10000000000 : ℝ)*X 2 1+(2454210427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-195298859/1000000000 : ℝ)*X 0 0+(126823303/250000000 : ℝ)*X 0 1+(1402689331/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628081857/5000000000 : ℝ)*X 1 0+(-1700847893/10000000000 : ℝ)*X 1 1+(5610757277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256164229/10000000000 : ℝ)*X 2 0+(5610757703/10000000000 : ℝ)*X 2 1+(-1700846551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141510501/5000000000 : ℝ)*X 0 0+(2447131367/5000000000 : ℝ)*X 0 1+(1871772331/5000000000 : ℝ)*X 0 2+(2141510501/5000000000 : ℝ)*X 1 0+(2447131367/5000000000 : ℝ)*X 1 1+(1871772331/5000000000 : ℝ)*X 1 2+(2141510501/5000000000 : ℝ)*X 2 0+(2447131367/5000000000 : ℝ)*X 2 1+(1871772331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2176265110149760676054305853/273700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3122087/20000000000000 : ℝ)*(base1) + (1416443331/100000000000000 : ℝ)*(base19) + (1726904741/100000000000000 : ℝ)*(base23) + (177089463/100000000000000 : ℝ)*(upper3) + (122421769/100000000000000 : ℝ)*(upper5) + (266232106334641/20000000000000 : ℝ)*(major0) + (266232106334641/20000000000000 : ℝ)*(major1) + (266232106334641/20000000000000 : ℝ)*(major2) + (453580052969701/25000000000000 : ℝ)*(sp0) + (181433270971583/10000000000000 : ℝ)*(sp1) + (90716619962721/5000000000000 : ℝ)*(sp2) + (52998815082849/6250000000000 : ℝ)*(sp3) + (1741236349/12500000000000 : ℝ)*(sp4) + (701901073/12500000000000 : ℝ)*(sp7) + (423993336072301/50000000000000 : ℝ)*(f.failure) + (907167063079581/50000000000000 : ℝ)*(f.sum) + (2074220001071/821100000000000000000000000 : ℝ)*base66 + (3624064327146094147/1642200000000000000000000000000000 : ℝ)*base68 + (13229867521182094147/1642200000000000000000000000000000 : ℝ)*base70 + (4620529990749505853/1642200000000000000000000000000000 : ℝ)*base71 + (280363551401/128296875000000000000000000 : ℝ)*base74 + (3568256311428094147/1642200000000000000000000000000000 : ℝ)*base76 + (2366059270244494147/1642200000000000000000000000000000 : ℝ)*base78 + (335195010526705853/1642200000000000000000000000000000 : ℝ)*base79 + (23997354301849/4105500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (940489/1000000000000000000000 : ℝ)*base89 + (940489/1000000000000000000000 : ℝ)*base91 + (940489/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2400508121525431573547956481/684250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5897901/3125000000000 : ℝ)*(base1) + (1048564661/100000000000000 : ℝ)*(base19) + (667937703/50000000000000 : ℝ)*(base23) + (39498931/50000000000000 : ℝ)*(upper3) + (194488347/100000000000000 : ℝ)*(upper5) + (682091214723319/50000000000000 : ℝ)*(major0) + (682091214723319/50000000000000 : ℝ)*(major1) + (682091214723319/50000000000000 : ℝ)*(major2) + (4896954327/100000000000000 : ℝ)*(sp1) + (1748583117/20000000000000 : ℝ)*(sp2) + (1859342381548481/100000000000000 : ℝ)*(sp4) + (929668123648331/50000000000000 : ℝ)*(sp5) + (929666057012329/50000000000000 : ℝ)*(sp6) + (434511180201851/50000000000000 : ℝ)*(sp7) + (434511274568267/50000000000000 : ℝ)*(f.failure) + (1859342192815649/100000000000000 : ℝ)*(f.sum) + (6961993134251/20527500000000000000000000000 : ℝ)*base66 + (15378643769555381173/4105500000000000000000000000000000 : ℝ)*base68 + (31279707466745381173/4105500000000000000000000000000000 : ℝ)*base70 + (45884853383655881173/4105500000000000000000000000000000 : ℝ)*base72 + (52850570475953/41055000000000000000000000000 : ℝ)*base73 + (56071683909828881173/4105500000000000000000000000000000 : ℝ)*base76 + (51615098981781881173/4105500000000000000000000000000000 : ℝ)*base78 + (15250528353549881173/4105500000000000000000000000000000 : ℝ)*base80 + (17310175458413/41055000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3172337/1000000000000000000000 : ℝ)*base90 + (3172337/1000000000000000000000 : ℝ)*base92 + (3172337/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26467/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (917/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (381/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_s2_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-993991073/5000000000 : ℝ)*x 0 + (1093026293/2000000000 : ℝ)*x 1 + (5195901827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993991073/5000000000 : ℝ)^4359 ≤ (6052886185227/50000000000000 : ℝ)^3335 := by
    have hnat : (993991073 : ℕ)^4359*50000000000000^3335 ≤ 6052886185227^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993991073 5000000000 6052886185227 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093026293/2000000000 : ℝ)^4359 ≤ (22698743154299/50000000000000 : ℝ)^3335 := by
    have hnat : (1093026293 : ℕ)^4359*50000000000000^3335 ≤ 22698743154299^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093026293 2000000000 22698743154299 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195901827/10000000000 : ℝ)^4359 ≤ (21248370654847/50000000000000 : ℝ)^3335 := by
    have hnat : (5195901827 : ℕ)^4359*50000000000000^3335 ≤ 21248370654847^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195901827 10000000000 21248370654847 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993991073/5000000000 : ℝ), (1093026293/2000000000 : ℝ), (5195901827/10000000000 : ℝ)] ![(6052886185227/50000000000000 : ℝ), (22698743154299/50000000000000 : ℝ), (21248370654847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993991073/5000000000 : ℝ)|^4359 ≤ (6052886185227/50000000000000 : ℝ)^3335
        have hw : |(-993991073/5000000000 : ℝ)|=(993991073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093026293/2000000000 : ℝ)|^4359 ≤ (22698743154299/50000000000000 : ℝ)^3335
        have hw : |(1093026293/2000000000 : ℝ)|=(1093026293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195901827/10000000000 : ℝ)|^4359 ≤ (21248370654847/50000000000000 : ℝ)^3335
        have hw : |(5195901827/10000000000 : ℝ)|=(5195901827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362076313/10000000000 : ℝ)*x 0 + (-531672501/2500000000 : ℝ)*x 1 + (5195901809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362076313/10000000000 : ℝ)^4359 ≤ (44281838016397/100000000000000 : ℝ)^3335 := by
    have hnat : (5362076313 : ℕ)^4359*100000000000000^3335 ≤ 44281838016397^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362076313 10000000000 44281838016397 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531672501/2500000000 : ℝ)^4359 ≤ (661071043209/5000000000000 : ℝ)^3335 := by
    have hnat : (531672501 : ℕ)^4359*5000000000000^3335 ≤ 661071043209^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531672501 2500000000 661071043209 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195901809/10000000000 : ℝ)^4359 ≤ (4249674111727/10000000000000 : ℝ)^3335 := by
    have hnat : (5195901809 : ℕ)^4359*10000000000000^3335 ≤ 4249674111727^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195901809 10000000000 4249674111727 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362076313/10000000000 : ℝ), (-531672501/2500000000 : ℝ), (5195901809/10000000000 : ℝ)] ![(44281838016397/100000000000000 : ℝ), (661071043209/5000000000000 : ℝ), (4249674111727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362076313/10000000000 : ℝ)|^4359 ≤ (44281838016397/100000000000000 : ℝ)^3335
        have hw : |(5362076313/10000000000 : ℝ)|=(5362076313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531672501/2500000000 : ℝ)|^4359 ≤ (661071043209/5000000000000 : ℝ)^3335
        have hw : |(-531672501/2500000000 : ℝ)|=(531672501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195901809/10000000000 : ℝ)|^4359 ≤ (4249674111727/10000000000000 : ℝ)^3335
        have hw : |(5195901809/10000000000 : ℝ)|=(5195901809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362076127/10000000000 : ℝ)*x 0 + (5195902017/10000000000 : ℝ)*x 1 + (-265836247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362076127/10000000000 : ℝ)^4359 ≤ (11070459002177/25000000000000 : ℝ)^3335 := by
    have hnat : (5362076127 : ℕ)^4359*25000000000000^3335 ≤ 11070459002177^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362076127 10000000000 11070459002177 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195902017/10000000000 : ℝ)^4359 ≤ (1328023229401/3125000000000 : ℝ)^3335 := by
    have hnat : (5195902017 : ℕ)^4359*3125000000000^3335 ≤ 1328023229401^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195902017 10000000000 1328023229401 3125000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265836247/1250000000 : ℝ)^4359 ≤ (6610710318329/50000000000000 : ℝ)^3335 := by
    have hnat : (265836247 : ℕ)^4359*50000000000000^3335 ≤ 6610710318329^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265836247 1250000000 6610710318329 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362076127/10000000000 : ℝ), (5195902017/10000000000 : ℝ), (-265836247/1250000000 : ℝ)] ![(11070459002177/25000000000000 : ℝ), (1328023229401/3125000000000 : ℝ), (6610710318329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362076127/10000000000 : ℝ)|^4359 ≤ (11070459002177/25000000000000 : ℝ)^3335
        have hw : |(5362076127/10000000000 : ℝ)|=(5362076127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195902017/10000000000 : ℝ)|^4359 ≤ (1328023229401/3125000000000 : ℝ)^3335
        have hw : |(5195902017/10000000000 : ℝ)|=(5195902017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265836247/1250000000 : ℝ)|^4359 ≤ (6610710318329/50000000000000 : ℝ)^3335
        have hw : |(-265836247/1250000000 : ℝ)|=(265836247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153504561/5000000000 : ℝ)*x 0 + (503468363/1250000000 : ℝ)*x 1 + (920757029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153504561/5000000000 : ℝ)^4359 ≤ (4156815705511/12500000000000 : ℝ)^3335 := by
    have hnat : (2153504561 : ℕ)^4359*12500000000000^3335 ≤ 4156815705511^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153504561 5000000000 4156815705511 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503468363/1250000000 : ℝ)^4359 ≤ (30464770023957/100000000000000 : ℝ)^3335 := by
    have hnat : (503468363 : ℕ)^4359*100000000000000^3335 ≤ 30464770023957^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503468363 1250000000 30464770023957 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920757029/2000000000 : ℝ)^4359 ≤ (9070176079491/25000000000000 : ℝ)^3335 := by
    have hnat : (920757029 : ℕ)^4359*25000000000000^3335 ≤ 9070176079491^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920757029 2000000000 9070176079491 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153504561/5000000000 : ℝ), (503468363/1250000000 : ℝ), (920757029/2000000000 : ℝ)] ![(4156815705511/12500000000000 : ℝ), (30464770023957/100000000000000 : ℝ), (9070176079491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153504561/5000000000 : ℝ)|^4359 ≤ (4156815705511/12500000000000 : ℝ)^3335
        have hw : |(2153504561/5000000000 : ℝ)|=(2153504561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503468363/1250000000 : ℝ)|^4359 ≤ (30464770023957/100000000000000 : ℝ)^3335
        have hw : |(503468363/1250000000 : ℝ)|=(503468363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920757029/2000000000 : ℝ)|^4359 ≤ (9070176079491/25000000000000 : ℝ)^3335
        have hw : |(920757029/2000000000 : ℝ)|=(920757029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988033351/10000000000 : ℝ)*x 0 + (1299372553/2500000000 : ℝ)*x 1 + (1092705969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988033351/10000000000 : ℝ)^4359 ≤ (12106179924437/100000000000000 : ℝ)^3335 := by
    have hnat : (1988033351 : ℕ)^4359*100000000000000^3335 ≤ 12106179924437^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988033351 10000000000 12106179924437 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299372553/2500000000 : ℝ)^4359 ≤ (21256861127843/50000000000000 : ℝ)^3335 := by
    have hnat : (1299372553 : ℕ)^4359*50000000000000^3335 ≤ 21256861127843^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299372553 2500000000 21256861127843 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092705969/2000000000 : ℝ)^4359 ≤ (45380097806761/100000000000000 : ℝ)^3335 := by
    have hnat : (1092705969 : ℕ)^4359*100000000000000^3335 ≤ 45380097806761^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092705969 2000000000 45380097806761 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988033351/10000000000 : ℝ), (1299372553/2500000000 : ℝ), (1092705969/2000000000 : ℝ)] ![(12106179924437/100000000000000 : ℝ), (21256861127843/50000000000000 : ℝ), (45380097806761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988033351/10000000000 : ℝ)|^4359 ≤ (12106179924437/100000000000000 : ℝ)^3335
        have hw : |(-1988033351/10000000000 : ℝ)|=(1988033351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299372553/2500000000 : ℝ)|^4359 ≤ (21256861127843/50000000000000 : ℝ)^3335
        have hw : |(1299372553/2500000000 : ℝ)|=(1299372553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092705969/2000000000 : ℝ)|^4359 ≤ (45380097806761/100000000000000 : ℝ)^3335
        have hw : |(1092705969/2000000000 : ℝ)|=(1092705969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66153379/125000000 : ℝ)*x 0 + (-929531289/5000000000 : ℝ)*x 1 + (1092705909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66153379/125000000 : ℝ)^4359 ≤ (43529860434997/100000000000000 : ℝ)^3335 := by
    have hnat : (66153379 : ℕ)^4359*100000000000000^3335 ≤ 43529860434997^3335*125000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66153379 125000000 43529860434997 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929531289/5000000000 : ℝ)^4359 ≤ (2218009001541/20000000000000 : ℝ)^3335 := by
    have hnat : (929531289 : ℕ)^4359*20000000000000^3335 ≤ 2218009001541^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929531289 5000000000 2218009001541 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092705909/2000000000 : ℝ)^4359 ≤ (45380094549861/100000000000000 : ℝ)^3335 := by
    have hnat : (1092705909 : ℕ)^4359*100000000000000^3335 ≤ 45380094549861^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092705909 2000000000 45380094549861 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66153379/125000000 : ℝ), (-929531289/5000000000 : ℝ), (1092705909/2000000000 : ℝ)] ![(43529860434997/100000000000000 : ℝ), (2218009001541/20000000000000 : ℝ), (45380094549861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66153379/125000000 : ℝ)|^4359 ≤ (43529860434997/100000000000000 : ℝ)^3335
        have hw : |(66153379/125000000 : ℝ)|=(66153379/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-929531289/5000000000 : ℝ)|^4359 ≤ (2218009001541/20000000000000 : ℝ)^3335
        have hw : |(-929531289/5000000000 : ℝ)|=(929531289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092705909/2000000000 : ℝ)|^4359 ≤ (45380094549861/100000000000000 : ℝ)^3335
        have hw : |(1092705909/2000000000 : ℝ)|=(1092705909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646135867/5000000000 : ℝ)*x 0 + (5463529529/10000000000 : ℝ)*x 1 + (-37181213/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646135867/5000000000 : ℝ)^4359 ≤ (43529875636471/100000000000000 : ℝ)^3335 := by
    have hnat : (2646135867 : ℕ)^4359*100000000000000^3335 ≤ 43529875636471^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646135867 5000000000 43529875636471 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463529529/10000000000 : ℝ)^4359 ≤ (283625589851/625000000000 : ℝ)^3335 := by
    have hnat : (5463529529 : ℕ)^4359*625000000000^3335 ≤ 283625589851^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463529529 10000000000 283625589851 625000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37181213/200000000 : ℝ)^4359 ≤ (5545014987497/50000000000000 : ℝ)^3335 := by
    have hnat : (37181213 : ℕ)^4359*50000000000000^3335 ≤ 5545014987497^3335*200000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37181213 200000000 5545014987497 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646135867/5000000000 : ℝ), (5463529529/10000000000 : ℝ), (-37181213/200000000 : ℝ)] ![(43529875636471/100000000000000 : ℝ), (283625589851/625000000000 : ℝ), (5545014987497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646135867/5000000000 : ℝ)|^4359 ≤ (43529875636471/100000000000000 : ℝ)^3335
        have hw : |(2646135867/5000000000 : ℝ)|=(2646135867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463529529/10000000000 : ℝ)|^4359 ≤ (283625589851/625000000000 : ℝ)^3335
        have hw : |(5463529529/10000000000 : ℝ)|=(5463529529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37181213/200000000 : ℝ)|^4359 ≤ (5545014987497/50000000000000 : ℝ)^3335
        have hw : |(-37181213/200000000 : ℝ)|=(37181213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s2_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538389999/1250000000 : ℝ)*x 0 + (4600387181/10000000000 : ℝ)*x 1 + (4031173209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538389999/1250000000 : ℝ)^4359 ≤ (16627822259789/50000000000000 : ℝ)^3335 := by
    have hnat : (538389999 : ℕ)^4359*50000000000000^3335 ≤ 16627822259789^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538389999 1250000000 16627822259789 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4600387181/10000000000 : ℝ)^4359 ≤ (3624570808941/10000000000000 : ℝ)^3335 := by
    have hnat : (4600387181 : ℕ)^4359*10000000000000^3335 ≤ 3624570808941^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4600387181 10000000000 3624570808941 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031173209/10000000000 : ℝ)^4359 ≤ (30498647378219/100000000000000 : ℝ)^3335 := by
    have hnat : (4031173209 : ℕ)^4359*100000000000000^3335 ≤ 30498647378219^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031173209 10000000000 30498647378219 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538389999/1250000000 : ℝ), (4600387181/10000000000 : ℝ), (4031173209/10000000000 : ℝ)] ![(16627822259789/50000000000000 : ℝ), (3624570808941/10000000000000 : ℝ), (30498647378219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538389999/1250000000 : ℝ)|^4359 ≤ (16627822259789/50000000000000 : ℝ)^3335
        have hw : |(538389999/1250000000 : ℝ)|=(538389999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4600387181/10000000000 : ℝ)|^4359 ≤ (3624570808941/10000000000000 : ℝ)^3335
        have hw : |(4600387181/10000000000 : ℝ)|=(4600387181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031173209/10000000000 : ℝ)|^4359 ≤ (30498647378219/100000000000000 : ℝ)^3335
        have hw : |(4031173209/10000000000 : ℝ)|=(4031173209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (381/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1987/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (381/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (381/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (381/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (381/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (381/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (381/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7399/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (1539428160685021/100000000000000000000 : ℝ) := by
    have hpowers : (7399/100000 : ℝ)^2179 ≤ (1539428160685021/100000000000000000000 : ℝ)^512 := by
      have hnat : (7399 : ℕ)^2179*100000000000000000000^512 ≤ 1539428160685021^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7399 100000 1539428160685021 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7399/100000 : ℝ)) (X := (1539428160685021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (381/2000 : ℝ) ^ (2179/512 : ℝ) ≤ (86165676028346367/100000000000000000000 : ℝ) := by
    have hpowers : (381/2000 : ℝ)^2179 ≤ (86165676028346367/100000000000000000000 : ℝ)^512 := by
      have hnat : (381 : ℕ)^2179*100000000000000000000^512 ≤ 86165676028346367^512*2000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 2000 86165676028346367 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/2000 : ℝ)) (X := (86165676028346367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001539428160685021/50000000000000000000 : ℝ) ≤ (5000036171543639/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50001539428160685021/50000000000000000000 : ℝ)^512 ≤ (5000036171543639/5000000000000000 : ℝ)^2179 := by
      have hnat : (50001539428160685021 : ℕ)^512*5000000000000000^2179 ≤ 5000036171543639^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001539428160685021 50000000000000000000 5000036171543639 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036171543639/5000000000000000 : ℝ)) (X := (50001539428160685021/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25021926276047257847/25000000000000000000 : ℝ) ≤ (5001030058654213/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (25021926276047257847/25000000000000000000 : ℝ)^512 ≤ (5001030058654213/5000000000000000 : ℝ)^2179 := by
      have hnat : (25021926276047257847 : ℕ)^512*5000000000000000^2179 ≤ 5001030058654213^2179*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021926276047257847 25000000000000000000 5001030058654213 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001030058654213/5000000000000000 : ℝ)) (X := (25021926276047257847/25000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50086165676028346367/50000000000000000000 : ℝ) ≤ (5002023945764787/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50086165676028346367/50000000000000000000 : ℝ)^512 ≤ (5002023945764787/5000000000000000 : ℝ)^2179 := by
      have hnat : (50086165676028346367 : ℕ)^512*5000000000000000^2179 ≤ 5002023945764787^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086165676028346367 50000000000000000000 5002023945764787 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002023945764787/5000000000000000 : ℝ)) (X := (50086165676028346367/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1539428160685021/100000000000000000000 : ℝ) ≤ ((58240713893192663937/58255000000000000000 : ℝ)+2*(496943555287/291275000000000 : ℝ)*(7399/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (58240713893192663937/58255000000000000000 : ℝ)+2*(496943555287/291275000000000 : ℝ)*(7399/100000 : ℝ)=(5000036171543639/5000000000000000 : ℝ) by norm_num, show 1+2*(1539428160685021/100000000000000000000 : ℝ)=(50001539428160685021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(86165676028346367/100000000000000000000 : ℝ)+(1539428160685021/100000000000000000000 : ℝ) ≤ ((58240713893192663937/58255000000000000000 : ℝ)+(496943555287/291275000000000 : ℝ)*((381/2000 : ℝ)+(7399/100000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (58240713893192663937/58255000000000000000 : ℝ)+(496943555287/291275000000000 : ℝ)*((381/2000 : ℝ)+(7399/100000 : ℝ))=(5001030058654213/5000000000000000 : ℝ) by norm_num, show 1+(86165676028346367/100000000000000000000 : ℝ)+(1539428160685021/100000000000000000000 : ℝ)=(25021926276047257847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(86165676028346367/100000000000000000000 : ℝ) ≤ ((58240713893192663937/58255000000000000000 : ℝ)+2*(496943555287/291275000000000 : ℝ)*(381/2000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (58240713893192663937/58255000000000000000 : ℝ)+2*(496943555287/291275000000000 : ℝ)*(381/2000 : ℝ)=(5002023945764787/5000000000000000 : ℝ) by norm_num, show 1+2*(86165676028346367/100000000000000000000 : ℝ)=(50086165676028346367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58240713893192663937/58255000000000000000 : ℝ)*(X 1 0+X 2 0)+(496943555287/291275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (7399/100000 : ℝ)) (hi := (381/2000 : ℝ)) (c := (58240713893192663937/58255000000000000000 : ℝ)) (alpha := (496943555287/291275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58240713893192663937/58255000000000000000 : ℝ)*(X 0 1+X 2 1)+(496943555287/291275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (7399/100000 : ℝ)) (hi := (381/2000 : ℝ)) (c := (58240713893192663937/58255000000000000000 : ℝ)) (alpha := (496943555287/291275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58240713893192663937/58255000000000000000 : ℝ)*(X 0 2+X 1 2)+(496943555287/291275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (7399/100000 : ℝ)) (hi := (381/2000 : ℝ)) (c := (58240713893192663937/58255000000000000000 : ℝ)) (alpha := (496943555287/291275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-993991073/5000000000 : ℝ)*X 0 0+(1093026293/2000000000 : ℝ)*X 0 1+(5195901827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362076313/10000000000 : ℝ)*X 1 0+(-531672501/2500000000 : ℝ)*X 1 1+(5195901809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362076127/10000000000 : ℝ)*X 2 0+(5195902017/10000000000 : ℝ)*X 2 1+(-265836247/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153504561/5000000000 : ℝ)*X 0 0+(503468363/1250000000 : ℝ)*X 0 1+(920757029/2000000000 : ℝ)*X 0 2+(2153504561/5000000000 : ℝ)*X 1 0+(503468363/1250000000 : ℝ)*X 1 1+(920757029/2000000000 : ℝ)*X 1 2+(2153504561/5000000000 : ℝ)*X 2 0+(503468363/1250000000 : ℝ)*X 2 1+(920757029/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988033351/10000000000 : ℝ)*X 0 0+(1299372553/2500000000 : ℝ)*X 0 1+(1092705969/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66153379/125000000 : ℝ)*X 1 0+(-929531289/5000000000 : ℝ)*X 1 1+(1092705909/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646135867/5000000000 : ℝ)*X 2 0+(5463529529/10000000000 : ℝ)*X 2 1+(-37181213/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538389999/1250000000 : ℝ)*X 0 0+(4600387181/10000000000 : ℝ)*X 0 1+(4031173209/10000000000 : ℝ)*X 0 2+(538389999/1250000000 : ℝ)*X 1 0+(4600387181/10000000000 : ℝ)*X 1 1+(4031173209/10000000000 : ℝ)*X 1 2+(538389999/1250000000 : ℝ)*X 2 0+(4600387181/10000000000 : ℝ)*X 2 1+(4031173209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5911876840044883073589808827/582550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1777924219/100000000000000 : ℝ)*(base19) + (1461762213/100000000000000 : ℝ)*(base23) + (100441689/100000000000000 : ℝ)*(lower2) + (14899481/5000000000000 : ℝ)*(upper3) + (144765407/100000000000000 : ℝ)*(upper5) + (545036242099657/20000000000000 : ℝ)*(major0) + (545036242099657/20000000000000 : ℝ)*(major1) + (545036242099657/20000000000000 : ℝ)*(major2) + (3714324527338473/100000000000000 : ℝ)*(sp0) + (3714343280030411/100000000000000 : ℝ)*(sp1) + (3714343596192417/100000000000000 : ℝ)*(sp2) + (868002768164739/50000000000000 : ℝ)*(sp3) + (20530616157/100000000000000 : ℝ)*(sp4) + (2872109167/25000000000000 : ℝ)*(sp7) + (868008512383073/50000000000000 : ℝ)*(f.failure) + (371434505795463/10000000000000 : ℝ)*(f.sum) + (19249694884879/11651000000000000000000000000 : ℝ)*base65 + (3608636058565869609/1165100000000000000000000000000000 : ℝ)*base67 + (3146183247470030391/1165100000000000000000000000000000 : ℝ)*base70 + (2101087109939269609/1165100000000000000000000000000000 : ℝ)*base71 + (931919761923/582550000000000000000000000 : ℝ)*base73 + (6377142636631330391/1165100000000000000000000000000000 : ℝ)*base76 + (3201719105632330391/1165100000000000000000000000000000 : ℝ)*base78 + (7082900433020130391/1165100000000000000000000000000000 : ℝ)*base80 + (14390630020903/5825500000000000000000000000 : ℝ)*base81 + (2920403/1000000000000000000000 : ℝ)*base90 + (2920403/1000000000000000000000 : ℝ)*base92 + (2920403/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4927965158716587825076991643/728187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (888091029/100000000000000 : ℝ)*(base19) + (1507581883/50000000000000 : ℝ)*(base23) + (21558197/10000000000000 : ℝ)*(upper3) + (309059711/100000000000000 : ℝ)*(lower4) + (27316591/50000000000000 : ℝ)*(upper5) + (689456195705129/25000000000000 : ℝ)*(major0) + (689456195705129/25000000000000 : ℝ)*(major1) + (689456195705129/25000000000000 : ℝ)*(major2) + (2784942243/100000000000000 : ℝ)*(sp1) + (5454278111/12500000000000 : ℝ)*(sp2) + (375883744224721/10000000000000 : ℝ)*(sp4) + (3758833769213939/100000000000000 : ℝ)*(sp5) + (939697698214639/25000000000000 : ℝ)*(sp6) + (439202974453121/25000000000000 : ℝ)*(sp7) + (439202974453121/25000000000000 : ℝ)*(f.failure) + (375883744224721/10000000000000 : ℝ)*(f.sum) + (106005417511611/29127500000000000000000000000 : ℝ)*base66 + (9055340292958332873/1456375000000000000000000000000000 : ℝ)*base67 + (865055053860582873/1456375000000000000000000000000000 : ℝ)*base69 + (2469198141646707873/1456375000000000000000000000000000 : ℝ)*base71 + (187536445555209/29127500000000000000000000000 : ℝ)*base73 + (1136577397024082873/1456375000000000000000000000000000 : ℝ)*base75 + (11630489629522832873/1456375000000000000000000000000000 : ℝ)*base77 + (9699362862245832873/1456375000000000000000000000000000 : ℝ)*base79 + (21762265680993/14563750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2692531/500000000000000000000 : ℝ)*base90 + (2692531/500000000000000000000 : ℝ)*base92 + (2692531/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (381/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1399_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1399_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1399_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1399_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
