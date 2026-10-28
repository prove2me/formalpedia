-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:26.290622+00:00
-- url     : https://prove2.me/submissions/e30c5b1d-ae2e-4dfb-8a5e-37d0c82a4c11

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
theorem support_rectangle_w1079_s0_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-955955329/5000000000 : ℝ)*x 0 + (6069006439/10000000000 : ℝ)*x 1 + (4772453231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955955329/5000000000 : ℝ)^517 ≤ (1386581336549/12500000000000 : ℝ)^389 := by
    have hnat : (955955329 : ℕ)^517*12500000000000^389 ≤ 1386581336549^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955955329 5000000000 1386581336549 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6069006439/10000000000 : ℝ)^517 ≤ (51493533572213/100000000000000 : ℝ)^389 := by
    have hnat : (6069006439 : ℕ)^517*100000000000000^389 ≤ 51493533572213^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6069006439 10000000000 51493533572213 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772453231/10000000000 : ℝ)^517 ≤ (37413815726887/100000000000000 : ℝ)^389 := by
    have hnat : (4772453231 : ℕ)^517*100000000000000^389 ≤ 37413815726887^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772453231 10000000000 37413815726887 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955955329/5000000000 : ℝ), (6069006439/10000000000 : ℝ), (4772453231/10000000000 : ℝ)] ![(1386581336549/12500000000000 : ℝ), (51493533572213/100000000000000 : ℝ), (37413815726887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955955329/5000000000 : ℝ)|^517 ≤ (1386581336549/12500000000000 : ℝ)^389
        have hw : |(-955955329/5000000000 : ℝ)|=(955955329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6069006439/10000000000 : ℝ)|^517 ≤ (51493533572213/100000000000000 : ℝ)^389
        have hw : |(6069006439/10000000000 : ℝ)|=(6069006439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772453231/10000000000 : ℝ)|^517 ≤ (37413815726887/100000000000000 : ℝ)^389
        have hw : |(4772453231/10000000000 : ℝ)|=(4772453231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1104068153/2000000000 : ℝ)*x 0 + (-2657829761/10000000000 : ℝ)*x 1 + (4772452699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104068153/2000000000 : ℝ)^517 ≤ (45400439885501/100000000000000 : ℝ)^389 := by
    have hnat : (1104068153 : ℕ)^517*100000000000000^389 ≤ 45400439885501^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104068153 2000000000 45400439885501 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2657829761/10000000000 : ℝ)^517 ≤ (17185749921683/100000000000000 : ℝ)^389 := by
    have hnat : (2657829761 : ℕ)^517*100000000000000^389 ≤ 17185749921683^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2657829761 10000000000 17185749921683 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772452699/10000000000 : ℝ)^517 ≤ (4676726272989/12500000000000 : ℝ)^389 := by
    have hnat : (4772452699 : ℕ)^517*12500000000000^389 ≤ 4676726272989^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772452699 10000000000 4676726272989 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104068153/2000000000 : ℝ), (-2657829761/10000000000 : ℝ), (4772452699/10000000000 : ℝ)] ![(45400439885501/100000000000000 : ℝ), (17185749921683/100000000000000 : ℝ), (4676726272989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104068153/2000000000 : ℝ)|^517 ≤ (45400439885501/100000000000000 : ℝ)^389
        have hw : |(1104068153/2000000000 : ℝ)|=(1104068153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2657829761/10000000000 : ℝ)|^517 ≤ (17185749921683/100000000000000 : ℝ)^389
        have hw : |(-2657829761/10000000000 : ℝ)|=(2657829761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772452699/10000000000 : ℝ)|^517 ≤ (4676726272989/12500000000000 : ℝ)^389
        have hw : |(4772452699/10000000000 : ℝ)|=(4772452699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1104068463/2000000000 : ℝ)*x 0 + (596556521/1250000000 : ℝ)*x 1 + (-166114277/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104068463/2000000000 : ℝ)^517 ≤ (9080091365517/20000000000000 : ℝ)^389 := by
    have hnat : (1104068463 : ℕ)^517*20000000000000^389 ≤ 9080091365517^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104068463 2000000000 9080091365517 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596556521/1250000000 : ℝ)^517 ≤ (37413804651357/100000000000000 : ℝ)^389 := by
    have hnat : (596556521 : ℕ)^517*100000000000000^389 ≤ 37413804651357^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596556521 1250000000 37413804651357 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166114277/625000000 : ℝ)^517 ≤ (8592869250301/50000000000000 : ℝ)^389 := by
    have hnat : (166114277 : ℕ)^517*50000000000000^389 ≤ 8592869250301^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166114277 625000000 8592869250301 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104068463/2000000000 : ℝ), (596556521/1250000000 : ℝ), (-166114277/625000000 : ℝ)] ![(9080091365517/20000000000000 : ℝ), (37413804651357/100000000000000 : ℝ), (8592869250301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104068463/2000000000 : ℝ)|^517 ≤ (9080091365517/20000000000000 : ℝ)^389
        have hw : |(1104068463/2000000000 : ℝ)|=(1104068463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596556521/1250000000 : ℝ)|^517 ≤ (37413804651357/100000000000000 : ℝ)^389
        have hw : |(596556521/1250000000 : ℝ)|=(596556521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166114277/625000000 : ℝ)|^517 ≤ (8592869250301/50000000000000 : ℝ)^389
        have hw : |(-166114277/625000000 : ℝ)|=(166114277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1051532939/2500000000 : ℝ)*x 0 + (3124183143/10000000000 : ℝ)*x 1 + (567180339/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051532939/2500000000 : ℝ)^517 ≤ (31631658777221/100000000000000 : ℝ)^389 := by
    have hnat : (1051532939 : ℕ)^517*100000000000000^389 ≤ 31631658777221^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051532939 2500000000 31631658777221 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124183143/10000000000 : ℝ)^517 ≤ (21304929899977/100000000000000 : ℝ)^389 := by
    have hnat : (3124183143 : ℕ)^517*100000000000000^389 ≤ 21304929899977^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124183143 10000000000 21304929899977 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567180339/1000000000 : ℝ)^517 ≤ (23531705653213/50000000000000 : ℝ)^389 := by
    have hnat : (567180339 : ℕ)^517*50000000000000^389 ≤ 23531705653213^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567180339 1000000000 23531705653213 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051532939/2500000000 : ℝ), (3124183143/10000000000 : ℝ), (567180339/1000000000 : ℝ)] ![(31631658777221/100000000000000 : ℝ), (21304929899977/100000000000000 : ℝ), (23531705653213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051532939/2500000000 : ℝ)|^517 ≤ (31631658777221/100000000000000 : ℝ)^389
        have hw : |(1051532939/2500000000 : ℝ)|=(1051532939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124183143/10000000000 : ℝ)|^517 ≤ (21304929899977/100000000000000 : ℝ)^389
        have hw : |(3124183143/10000000000 : ℝ)|=(3124183143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567180339/1000000000 : ℝ)|^517 ≤ (23531705653213/50000000000000 : ℝ)^389
        have hw : |(567180339/1000000000 : ℝ)|=(567180339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-59913917/312500000 : ℝ)*x 0 + (4805926389/10000000000 : ℝ)*x 1 + (377147541/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59913917/312500000 : ℝ)^517 ≤ (1113380513699/10000000000000 : ℝ)^389 := by
    have hnat : (59913917 : ℕ)^517*10000000000000^389 ≤ 1113380513699^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59913917 312500000 1113380513699 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805926389/10000000000 : ℝ)^517 ≤ (18881489289139/50000000000000 : ℝ)^389 := by
    have hnat : (4805926389 : ℕ)^517*50000000000000^389 ≤ 18881489289139^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805926389 10000000000 18881489289139 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377147541/625000000 : ℝ)^517 ≤ (25551608131593/50000000000000 : ℝ)^389 := by
    have hnat : (377147541 : ℕ)^517*50000000000000^389 ≤ 25551608131593^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377147541 625000000 25551608131593 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59913917/312500000 : ℝ), (4805926389/10000000000 : ℝ), (377147541/625000000 : ℝ)] ![(1113380513699/10000000000000 : ℝ), (18881489289139/50000000000000 : ℝ), (25551608131593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59913917/312500000 : ℝ)|^517 ≤ (1113380513699/10000000000000 : ℝ)^389
        have hw : |(-59913917/312500000 : ℝ)|=(59913917/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805926389/10000000000 : ℝ)|^517 ≤ (18881489289139/50000000000000 : ℝ)^389
        have hw : |(4805926389/10000000000 : ℝ)|=(4805926389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377147541/625000000 : ℝ)|^517 ≤ (25551608131593/50000000000000 : ℝ)^389
        have hw : |(377147541/625000000 : ℝ)|=(377147541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5168365779/10000000000 : ℝ)*x 0 + (-69796211/500000000 : ℝ)*x 1 + (3017179381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168365779/10000000000 : ℝ)^517 ≤ (41594169589581/100000000000000 : ℝ)^389 := by
    have hnat : (5168365779 : ℕ)^517*100000000000000^389 ≤ 41594169589581^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168365779 10000000000 41594169589581 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69796211/500000000 : ℝ)^517 ≤ (7302635450309/100000000000000 : ℝ)^389 := by
    have hnat : (69796211 : ℕ)^517*100000000000000^389 ≤ 7302635450309^389*500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69796211 500000000 7302635450309 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3017179381/5000000000 : ℝ)^517 ≤ (51103194945607/100000000000000 : ℝ)^389 := by
    have hnat : (3017179381 : ℕ)^517*100000000000000^389 ≤ 51103194945607^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017179381 5000000000 51103194945607 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168365779/10000000000 : ℝ), (-69796211/500000000 : ℝ), (3017179381/5000000000 : ℝ)] ![(41594169589581/100000000000000 : ℝ), (7302635450309/100000000000000 : ℝ), (51103194945607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168365779/10000000000 : ℝ)|^517 ≤ (41594169589581/100000000000000 : ℝ)^389
        have hw : |(5168365779/10000000000 : ℝ)|=(5168365779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69796211/500000000 : ℝ)|^517 ≤ (7302635450309/100000000000000 : ℝ)^389
        have hw : |(-69796211/500000000 : ℝ)|=(69796211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3017179381/5000000000 : ℝ)|^517 ≤ (51103194945607/100000000000000 : ℝ)^389
        have hw : |(3017179381/5000000000 : ℝ)|=(3017179381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5168365699/10000000000 : ℝ)*x 0 + (6034360273/10000000000 : ℝ)*x 1 + (-697960949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168365699/10000000000 : ℝ)^517 ≤ (41594168733903/100000000000000 : ℝ)^389 := by
    have hnat : (5168365699 : ℕ)^517*100000000000000^389 ≤ 41594168733903^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168365699 10000000000 41594168733903 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6034360273/10000000000 : ℝ)^517 ≤ (51103211952397/100000000000000 : ℝ)^389 := by
    have hnat : (6034360273 : ℕ)^517*100000000000000^389 ≤ 51103211952397^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034360273 10000000000 51103211952397 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697960949/5000000000 : ℝ)^517 ≤ (146052386119/2000000000000 : ℝ)^389 := by
    have hnat : (697960949 : ℕ)^517*2000000000000^389 ≤ 146052386119^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697960949 5000000000 146052386119 2000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168365699/10000000000 : ℝ), (6034360273/10000000000 : ℝ), (-697960949/5000000000 : ℝ)] ![(41594168733903/100000000000000 : ℝ), (51103211952397/100000000000000 : ℝ), (146052386119/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168365699/10000000000 : ℝ)|^517 ≤ (41594168733903/100000000000000 : ℝ)^389
        have hw : |(5168365699/10000000000 : ℝ)|=(5168365699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6034360273/10000000000 : ℝ)|^517 ≤ (51103211952397/100000000000000 : ℝ)^389
        have hw : |(6034360273/10000000000 : ℝ)|=(6034360273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-697960949/5000000000 : ℝ)|^517 ≤ (146052386119/2000000000000 : ℝ)^389
        have hw : |(-697960949/5000000000 : ℝ)|=(697960949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s0_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (527076807/1250000000 : ℝ)*x 0 + (140150701/250000000 : ℝ)*x 1 + (319225749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527076807/1250000000 : ℝ)^517 ≤ (31736475634333/100000000000000 : ℝ)^389 := by
    have hnat : (527076807 : ℕ)^517*100000000000000^389 ≤ 31736475634333^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527076807 1250000000 31736475634333 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140150701/250000000 : ℝ)^517 ≤ (46339417640003/100000000000000 : ℝ)^389 := by
    have hnat : (140150701 : ℕ)^517*100000000000000^389 ≤ 46339417640003^389*250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140150701 250000000 46339417640003 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319225749/1000000000 : ℝ)^517 ≤ (21924106703763/100000000000000 : ℝ)^389 := by
    have hnat : (319225749 : ℕ)^517*100000000000000^389 ≤ 21924106703763^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319225749 1000000000 21924106703763 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527076807/1250000000 : ℝ), (140150701/250000000 : ℝ), (319225749/1000000000 : ℝ)] ![(31736475634333/100000000000000 : ℝ), (46339417640003/100000000000000 : ℝ), (21924106703763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527076807/1250000000 : ℝ)|^517 ≤ (31736475634333/100000000000000 : ℝ)^389
        have hw : |(527076807/1250000000 : ℝ)|=(527076807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140150701/250000000 : ℝ)|^517 ≤ (46339417640003/100000000000000 : ℝ)^389
        have hw : |(140150701/250000000 : ℝ)|=(140150701/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319225749/1000000000 : ℝ)|^517 ≤ (21924106703763/100000000000000 : ℝ)^389
        have hw : |(319225749/1000000000 : ℝ)|=(319225749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (151/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8271/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8271 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8271*1^2048 ≤ 0^2048*1^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8271/2048 : ℝ) ≤ (308887087242677039/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8271 ≤ (308887087242677039/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8271*12500000000000000000^2048 ≤ 308887087242677039^2048*5^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 308887087242677039 12500000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (308887087242677039/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8271 := by
      have hnat : (1 : ℕ)^2048*1^8271 ≤ 1^8271*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12808887087242677039/12500000000000000000 : ℝ) ≤ (5030313311208793/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (12808887087242677039/12500000000000000000 : ℝ)^2048 ≤ (5030313311208793/5000000000000000 : ℝ)^8271 := by
      have hnat : (12808887087242677039 : ℕ)^2048*5000000000000000^8271 ≤ 5030313311208793^8271*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12808887087242677039 12500000000000000000 5030313311208793 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030313311208793/5000000000000000 : ℝ)) (X := (12808887087242677039/12500000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6558887087242677039/6250000000000000000 : ℝ) ≤ (2530313311208793/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (6558887087242677039/6250000000000000000 : ℝ)^2048 ≤ (2530313311208793/2500000000000000 : ℝ)^8271 := by
      have hnat : (6558887087242677039 : ℕ)^2048*2500000000000000^8271 ≤ 2530313311208793^8271*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6558887087242677039 6250000000000000000 2530313311208793 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530313311208793/2500000000000000 : ℝ)) (X := (6558887087242677039/6250000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30313311208793/2000000000000000 : ℝ)*(0 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30313311208793/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(308887087242677039/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30313311208793/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30313311208793/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030313311208793/5000000000000000 : ℝ) by norm_num, show 1+(308887087242677039/12500000000000000000 : ℝ)+(0 : ℝ)=(12808887087242677039/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(308887087242677039/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30313311208793/2000000000000000 : ℝ)*(2/5 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30313311208793/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530313311208793/2500000000000000 : ℝ) by norm_num, show 1+2*(308887087242677039/12500000000000000000 : ℝ)=(6558887087242677039/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30313311208793/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30313311208793/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30313311208793/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30313311208793/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30313311208793/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30313311208793/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-955955329/5000000000 : ℝ)*X 0 0+(6069006439/10000000000 : ℝ)*X 0 1+(4772453231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1104068153/2000000000 : ℝ)*X 1 0+(-2657829761/10000000000 : ℝ)*X 1 1+(4772452699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104068463/2000000000 : ℝ)*X 2 0+(596556521/1250000000 : ℝ)*X 2 1+(-166114277/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1051532939/2500000000 : ℝ)*X 0 0+(3124183143/10000000000 : ℝ)*X 0 1+(567180339/1000000000 : ℝ)*X 0 2+(1051532939/2500000000 : ℝ)*X 1 0+(3124183143/10000000000 : ℝ)*X 1 1+(567180339/1000000000 : ℝ)*X 1 2+(1051532939/2500000000 : ℝ)*X 2 0+(3124183143/10000000000 : ℝ)*X 2 1+(567180339/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-59913917/312500000 : ℝ)*X 0 0+(4805926389/10000000000 : ℝ)*X 0 1+(377147541/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168365779/10000000000 : ℝ)*X 1 0+(-69796211/500000000 : ℝ)*X 1 1+(3017179381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168365699/10000000000 : ℝ)*X 2 0+(6034360273/10000000000 : ℝ)*X 2 1+(-697960949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((527076807/1250000000 : ℝ)*X 0 0+(140150701/250000000 : ℝ)*X 0 1+(319225749/1000000000 : ℝ)*X 0 2+(527076807/1250000000 : ℝ)*X 1 0+(140150701/250000000 : ℝ)*X 1 1+(319225749/1000000000 : ℝ)*X 1 2+(527076807/1250000000 : ℝ)*X 2 0+(140150701/250000000 : ℝ)*X 2 1+(319225749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41299544664220440261717/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267764081/25000000000000 : ℝ)*(base19) + (648609677/50000000000000 : ℝ)*(base23) + (87801249/50000000000000 : ℝ)*(base24) + (190433857/100000000000000 : ℝ)*(base39) + (104916739/50000000000000 : ℝ)*(upper3) + (290952428783407/50000000000000 : ℝ)*(major0) + (290952428783407/50000000000000 : ℝ)*(major1) + (145476166783239/25000000000000 : ℝ)*(major2) + (771280280035639/100000000000000 : ℝ)*(sp0) + (15425633158463/2000000000000 : ℝ)*(sp1) + (19282036164787/2500000000000 : ℝ)*(sp2) + (24532776374241/6250000000000 : ℝ)*(sp3) + (489788767/20000000000000 : ℝ)*(sp4) + (2098402133/100000000000000 : ℝ)*(sp7) + (39252652038999/10000000000000 : ℝ)*(f.failure) + (192820729853333/25000000000000 : ℝ)*(f.sum) + (37537009267761/20000000000000000000000000000 : ℝ)*base65 + (543407398620527/50000000000000000000000000000 : ℝ)*base67 + (86562212997751/100000000000000000000000000000 : ℝ)*base69 + (375725525120527/50000000000000000000000000000 : ℝ)*base71 + (48395839347761/20000000000000000000000000000 : ℝ)*base73 + (573199564897751/100000000000000000000000000000 : ℝ)*base75 + (214546952497751/100000000000000000000000000000 : ℝ)*base77 + (798888614097751/100000000000000000000000000000 : ℝ)*base79 + (64901381602249/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (838001/500000000000000000000 : ℝ)*base89 + (838001/500000000000000000000 : ℝ)*base91 + (5838001/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173123824632990530063367/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (388790237/100000000000000 : ℝ)*(base19) + (315019083/100000000000000 : ℝ)*(base23) + (14510531/100000000000000 : ℝ)*(base39) + (2020429/3125000000000 : ℝ)*(upper4) + (88026019/50000000000000 : ℝ)*(upper5) + (614167669956373/100000000000000 : ℝ)*(major0) + (614167669956373/100000000000000 : ℝ)*(major1) + (307083827722921/50000000000000 : ℝ)*(major2) + (731833241/100000000000000 : ℝ)*(sp2) + (6619919/4000000000000 : ℝ)*(sp3) + (203511430781249/25000000000000 : ℝ)*(sp4) + (814045334334759/100000000000000 : ℝ)*(sp5) + (203511172695801/25000000000000 : ℝ)*(sp6) + (207144689535649/50000000000000 : ℝ)*(sp7) + (414289544569273/100000000000000 : ℝ)*(f.failure) + (814045737635527/100000000000000 : ℝ)*(f.sum) + (52529739375299/40000000000000000000000000000 : ℝ)*base65 + (246731896055647/100000000000000000000000000000 : ℝ)*base68 + (630548725212211/200000000000000000000000000000 : ℝ)*base70 + (344894157944353/100000000000000000000000000000 : ℝ)*base71 + (198478620664701/40000000000000000000000000000 : ℝ)*base74 + (66598921612211/200000000000000000000000000000 : ℝ)*base76 + (802003895812211/200000000000000000000000000000 : ℝ)*base78 + (1706706301012211/200000000000000000000000000000 : ℝ)*base80 + (73399407387789/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (28009727/5000000000000000000000 : ℝ)*base89 + (28009727/5000000000000000000000 : ℝ)*base91 + (28009727/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1079_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s1_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-212111847/1000000000 : ℝ)*x 0 + (5718679459/10000000000 : ℝ)*x 1 + (4988811243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212111847/1000000000 : ℝ)^517 ≤ (12734206656243/100000000000000 : ℝ)^389 := by
    have hnat : (212111847 : ℕ)^517*100000000000000^389 ≤ 12734206656243^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212111847 1000000000 12734206656243 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5718679459/10000000000 : ℝ)^517 ≤ (23790534938083/50000000000000 : ℝ)^389 := by
    have hnat : (5718679459 : ℕ)^517*50000000000000^389 ≤ 23790534938083^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718679459 10000000000 23790534938083 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988811243/10000000000 : ℝ)^517 ≤ (39684723454227/100000000000000 : ℝ)^389 := by
    have hnat : (4988811243 : ℕ)^517*100000000000000^389 ≤ 39684723454227^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988811243 10000000000 39684723454227 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212111847/1000000000 : ℝ), (5718679459/10000000000 : ℝ), (4988811243/10000000000 : ℝ)] ![(12734206656243/100000000000000 : ℝ), (23790534938083/50000000000000 : ℝ), (39684723454227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212111847/1000000000 : ℝ)|^517 ≤ (12734206656243/100000000000000 : ℝ)^389
        have hw : |(-212111847/1000000000 : ℝ)|=(212111847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5718679459/10000000000 : ℝ)|^517 ≤ (23790534938083/50000000000000 : ℝ)^389
        have hw : |(5718679459/10000000000 : ℝ)|=(5718679459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988811243/10000000000 : ℝ)|^517 ≤ (39684723454227/100000000000000 : ℝ)^389
        have hw : |(4988811243/10000000000 : ℝ)|=(4988811243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5422590713/10000000000 : ℝ)*x 0 + (-2516286749/10000000000 : ℝ)*x 1 + (199552461/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422590713/10000000000 : ℝ)^517 ≤ (4433512012213/10000000000000 : ℝ)^389 := by
    have hnat : (5422590713 : ℕ)^517*10000000000000^389 ≤ 4433512012213^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422590713 10000000000 4433512012213 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516286749/10000000000 : ℝ)^517 ≤ (3995038357221/25000000000000 : ℝ)^389 := by
    have hnat : (2516286749 : ℕ)^517*25000000000000^389 ≤ 3995038357221^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516286749 10000000000 3995038357221 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199552461/400000000 : ℝ)^517 ≤ (99211816089/250000000000 : ℝ)^389 := by
    have hnat : (199552461 : ℕ)^517*250000000000^389 ≤ 99211816089^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199552461 400000000 99211816089 250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422590713/10000000000 : ℝ), (-2516286749/10000000000 : ℝ), (199552461/400000000 : ℝ)] ![(4433512012213/10000000000000 : ℝ), (3995038357221/25000000000000 : ℝ), (99211816089/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422590713/10000000000 : ℝ)|^517 ≤ (4433512012213/10000000000000 : ℝ)^389
        have hw : |(5422590713/10000000000 : ℝ)|=(5422590713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2516286749/10000000000 : ℝ)|^517 ≤ (3995038357221/25000000000000 : ℝ)^389
        have hw : |(-2516286749/10000000000 : ℝ)|=(2516286749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199552461/400000000 : ℝ)|^517 ≤ (99211816089/250000000000 : ℝ)^389
        have hw : |(199552461/400000000 : ℝ)|=(199552461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5422591443/10000000000 : ℝ)*x 0 + (4988810741/10000000000 : ℝ)*x 1 + (-2516286791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422591443/10000000000 : ℝ)^517 ≤ (8867025610907/20000000000000 : ℝ)^389 := by
    have hnat : (5422591443 : ℕ)^517*20000000000000^389 ≤ 8867025610907^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422591443 10000000000 8867025610907 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988810741/10000000000 : ℝ)^517 ≤ (496058976837/1250000000000 : ℝ)^389 := by
    have hnat : (4988810741 : ℕ)^517*1250000000000^389 ≤ 496058976837^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988810741 10000000000 496058976837 1250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2516286791/10000000000 : ℝ)^517 ≤ (799007689169/5000000000000 : ℝ)^389 := by
    have hnat : (2516286791 : ℕ)^517*5000000000000^389 ≤ 799007689169^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516286791 10000000000 799007689169 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422591443/10000000000 : ℝ), (4988810741/10000000000 : ℝ), (-2516286791/10000000000 : ℝ)] ![(8867025610907/20000000000000 : ℝ), (496058976837/1250000000000 : ℝ), (799007689169/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422591443/10000000000 : ℝ)|^517 ≤ (8867025610907/20000000000000 : ℝ)^389
        have hw : |(5422591443/10000000000 : ℝ)|=(5422591443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988810741/10000000000 : ℝ)|^517 ≤ (496058976837/1250000000000 : ℝ)^389
        have hw : |(4988810741/10000000000 : ℝ)|=(4988810741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2516286791/10000000000 : ℝ)|^517 ≤ (799007689169/5000000000000 : ℝ)^389
        have hw : |(-2516286791/10000000000 : ℝ)|=(2516286791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (270170419/625000000 : ℝ)*x 0 + (1832534103/5000000000 : ℝ)*x 1 + (5099199393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270170419/625000000 : ℝ)^517 ≤ (8200575024323/25000000000000 : ℝ)^389 := by
    have hnat : (270170419 : ℕ)^517*25000000000000^389 ≤ 8200575024323^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270170419 625000000 8200575024323 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1832534103/5000000000 : ℝ)^517 ≤ (5268339615543/20000000000000 : ℝ)^389 := by
    have hnat : (1832534103 : ℕ)^517*20000000000000^389 ≤ 5268339615543^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832534103 5000000000 5268339615543 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099199393/10000000000 : ℝ)^517 ≤ (4085600180789/10000000000000 : ℝ)^389 := by
    have hnat : (5099199393 : ℕ)^517*10000000000000^389 ≤ 4085600180789^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099199393 10000000000 4085600180789 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270170419/625000000 : ℝ), (1832534103/5000000000 : ℝ), (5099199393/10000000000 : ℝ)] ![(8200575024323/25000000000000 : ℝ), (5268339615543/20000000000000 : ℝ), (4085600180789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270170419/625000000 : ℝ)|^517 ≤ (8200575024323/25000000000000 : ℝ)^389
        have hw : |(270170419/625000000 : ℝ)|=(270170419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1832534103/5000000000 : ℝ)|^517 ≤ (5268339615543/20000000000000 : ℝ)^389
        have hw : |(1832534103/5000000000 : ℝ)|=(1832534103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099199393/10000000000 : ℝ)|^517 ≤ (4085600180789/10000000000000 : ℝ)^389
        have hw : |(5099199393/10000000000 : ℝ)|=(5099199393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122016951/10000000000 : ℝ)*x 0 + (2499509367/5000000000 : ℝ)*x 1 + (5708265673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122016951/10000000000 : ℝ)^517 ≤ (1592672015817/12500000000000 : ℝ)^389 := by
    have hnat : (2122016951 : ℕ)^517*12500000000000^389 ≤ 1592672015817^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122016951 10000000000 1592672015817 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499509367/5000000000 : ℝ)^517 ≤ (39792675863267/100000000000000 : ℝ)^389 := by
    have hnat : (2499509367 : ℕ)^517*100000000000000^389 ≤ 39792675863267^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499509367 5000000000 39792675863267 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5708265673/10000000000 : ℝ)^517 ≤ (75945516803/160000000000 : ℝ)^389 := by
    have hnat : (5708265673 : ℕ)^517*160000000000^389 ≤ 75945516803^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708265673 10000000000 75945516803 160000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122016951/10000000000 : ℝ), (2499509367/5000000000 : ℝ), (5708265673/10000000000 : ℝ)] ![(1592672015817/12500000000000 : ℝ), (39792675863267/100000000000000 : ℝ), (75945516803/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122016951/10000000000 : ℝ)|^517 ≤ (1592672015817/12500000000000 : ℝ)^389
        have hw : |(-2122016951/10000000000 : ℝ)|=(2122016951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499509367/5000000000 : ℝ)|^517 ≤ (39792675863267/100000000000000 : ℝ)^389
        have hw : |(2499509367/5000000000 : ℝ)|=(2499509367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5708265673/10000000000 : ℝ)|^517 ≤ (75945516803/160000000000 : ℝ)^389
        have hw : |(5708265673/10000000000 : ℝ)|=(5708265673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1047213447/2000000000 : ℝ)*x 0 + (-56151013/312500000 : ℝ)*x 1 + (570826553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047213447/2000000000 : ℝ)^517 ≤ (42319858360147/100000000000000 : ℝ)^389 := by
    have hnat : (1047213447 : ℕ)^517*100000000000000^389 ≤ 42319858360147^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047213447 2000000000 42319858360147 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56151013/312500000 : ℝ)^517 ≤ (5107097603329/50000000000000 : ℝ)^389 := by
    have hnat : (56151013 : ℕ)^517*50000000000000^389 ≤ 5107097603329^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56151013 312500000 5107097603329 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570826553/1000000000 : ℝ)^517 ≤ (23732973210759/50000000000000 : ℝ)^389 := by
    have hnat : (570826553 : ℕ)^517*50000000000000^389 ≤ 23732973210759^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570826553 1000000000 23732973210759 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047213447/2000000000 : ℝ), (-56151013/312500000 : ℝ), (570826553/1000000000 : ℝ)] ![(42319858360147/100000000000000 : ℝ), (5107097603329/50000000000000 : ℝ), (23732973210759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047213447/2000000000 : ℝ)|^517 ≤ (42319858360147/100000000000000 : ℝ)^389
        have hw : |(1047213447/2000000000 : ℝ)|=(1047213447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56151013/312500000 : ℝ)|^517 ≤ (5107097603329/50000000000000 : ℝ)^389
        have hw : |(-56151013/312500000 : ℝ)|=(56151013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570826553/1000000000 : ℝ)|^517 ≤ (23732973210759/50000000000000 : ℝ)^389
        have hw : |(570826553/1000000000 : ℝ)|=(570826553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5236067251/10000000000 : ℝ)*x 0 + (5708265641/10000000000 : ℝ)*x 1 + (-179683223/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236067251/10000000000 : ℝ)^517 ≤ (42319858532017/100000000000000 : ℝ)^389 := by
    have hnat : (5236067251 : ℕ)^517*100000000000000^389 ≤ 42319858532017^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236067251 10000000000 42319858532017 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5708265641/10000000000 : ℝ)^517 ≤ (11866486912057/25000000000000 : ℝ)^389 := by
    have hnat : (5708265641 : ℕ)^517*25000000000000^389 ≤ 11866486912057^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708265641 10000000000 11866486912057 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179683223/1000000000 : ℝ)^517 ≤ (5107096900709/50000000000000 : ℝ)^389 := by
    have hnat : (179683223 : ℕ)^517*50000000000000^389 ≤ 5107096900709^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179683223 1000000000 5107096900709 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236067251/10000000000 : ℝ), (5708265641/10000000000 : ℝ), (-179683223/1000000000 : ℝ)] ![(42319858532017/100000000000000 : ℝ), (11866486912057/25000000000000 : ℝ), (5107096900709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236067251/10000000000 : ℝ)|^517 ≤ (42319858532017/100000000000000 : ℝ)^389
        have hw : |(5236067251/10000000000 : ℝ)|=(5236067251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5708265641/10000000000 : ℝ)|^517 ≤ (11866486912057/25000000000000 : ℝ)^389
        have hw : |(5708265641/10000000000 : ℝ)|=(5708265641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179683223/1000000000 : ℝ)|^517 ≤ (5107096900709/50000000000000 : ℝ)^389
        have hw : |(-179683223/1000000000 : ℝ)|=(179683223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s1_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (108112289/250000000 : ℝ)*x 0 + (5079143281/10000000000 : ℝ)*x 1 + (3685529787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108112289/250000000 : ℝ)^517 ≤ (32820100339197/100000000000000 : ℝ)^389 := by
    have hnat : (108112289 : ℕ)^517*100000000000000^389 ≤ 32820100339197^389*250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108112289 250000000 32820100339197 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079143281/10000000000 : ℝ)^517 ≤ (20321284744113/50000000000000 : ℝ)^389 := by
    have hnat : (5079143281 : ℕ)^517*50000000000000^389 ≤ 20321284744113^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079143281 10000000000 20321284744113 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685529787/10000000000 : ℝ)^517 ≤ (13268665076739/50000000000000 : ℝ)^389 := by
    have hnat : (3685529787 : ℕ)^517*50000000000000^389 ≤ 13268665076739^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685529787 10000000000 13268665076739 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108112289/250000000 : ℝ), (5079143281/10000000000 : ℝ), (3685529787/10000000000 : ℝ)] ![(32820100339197/100000000000000 : ℝ), (20321284744113/50000000000000 : ℝ), (13268665076739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108112289/250000000 : ℝ)|^517 ≤ (32820100339197/100000000000000 : ℝ)^389
        have hw : |(108112289/250000000 : ℝ)|=(108112289/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079143281/10000000000 : ℝ)|^517 ≤ (20321284744113/50000000000000 : ℝ)^389
        have hw : |(5079143281/10000000000 : ℝ)|=(5079143281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685529787/10000000000 : ℝ)|^517 ≤ (13268665076739/50000000000000 : ℝ)^389
        have hw : |(3685529787/10000000000 : ℝ)|=(3685529787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (529/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (151/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (404658837/100000000000000000000 : ℝ) := by
    have hpowers : (151/100000 : ℝ)^8271 ≤ (404658837/100000000000000000000 : ℝ)^2048 := by
      have hnat : (151 : ℕ)^8271*100000000000000000000^2048 ≤ 404658837^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        151 100000 404658837 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (151/100000 : ℝ)) (X := (404658837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/50000 : ℝ) ^ (8271/2048 : ℝ) ≤ (295057098043189973/50000000000000000000 : ℝ) := by
    have hpowers : (14029/50000 : ℝ)^8271 ≤ (295057098043189973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14029 : ℕ)^8271*50000000000000000000^2048 ≤ 295057098043189973^2048*50000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 50000 295057098043189973 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/50000 : ℝ)) (X := (295057098043189973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000404658837/50000000000000000000 : ℝ) ≤ (250000000000501/250000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50000000000404658837/50000000000000000000 : ℝ)^2048 ≤ (250000000000501/250000000000000 : ℝ)^8271 := by
      have hnat : (50000000000404658837 : ℕ)^2048*250000000000000^8271 ≤ 250000000000501^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000404658837 50000000000000000000 250000000000501 250000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000000000501/250000000000000 : ℝ)) (X := (50000000000404658837/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100590114196491038783/100000000000000000000 : ℝ) ≤ (1251822452132959/1250000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100590114196491038783/100000000000000000000 : ℝ)^2048 ≤ (1251822452132959/1250000000000000 : ℝ)^8271 := by
      have hnat : (100590114196491038783 : ℕ)^2048*1250000000000000^8271 ≤ 1251822452132959^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100590114196491038783 100000000000000000000 1251822452132959 1250000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251822452132959/1250000000000000 : ℝ)) (X := (100590114196491038783/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25295057098043189973/25000000000000000000 : ℝ) ≤ (1253644904263413/1250000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25295057098043189973/25000000000000000000 : ℝ)^2048 ≤ (1253644904263413/1250000000000000 : ℝ)^8271 := by
      have hnat : (25295057098043189973 : ℕ)^2048*1250000000000000^8271 ≤ 1253644904263413^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25295057098043189973 25000000000000000000 1253644904263413 1250000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253644904263413/1250000000000000 : ℝ)) (X := (25295057098043189973/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(404658837/100000000000000000000 : ℝ) ≤ ((34883199619526509927/34883750000000000000 : ℝ)+2*(911226065227/174418750000000 : ℝ)*(151/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (34883199619526509927/34883750000000000000 : ℝ)+2*(911226065227/174418750000000 : ℝ)*(151/100000 : ℝ)=(250000000000501/250000000000000 : ℝ) by norm_num, show 1+2*(404658837/100000000000000000000 : ℝ)=(50000000000404658837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(295057098043189973/50000000000000000000 : ℝ)+(404658837/100000000000000000000 : ℝ) ≤ ((34883199619526509927/34883750000000000000 : ℝ)+(911226065227/174418750000000 : ℝ)*((14029/50000 : ℝ)+(151/100000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (34883199619526509927/34883750000000000000 : ℝ)+(911226065227/174418750000000 : ℝ)*((14029/50000 : ℝ)+(151/100000 : ℝ))=(1251822452132959/1250000000000000 : ℝ) by norm_num, show 1+(295057098043189973/50000000000000000000 : ℝ)+(404658837/100000000000000000000 : ℝ)=(100590114196491038783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(295057098043189973/50000000000000000000 : ℝ) ≤ ((34883199619526509927/34883750000000000000 : ℝ)+2*(911226065227/174418750000000 : ℝ)*(14029/50000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (34883199619526509927/34883750000000000000 : ℝ)+2*(911226065227/174418750000000 : ℝ)*(14029/50000 : ℝ)=(1253644904263413/1250000000000000 : ℝ) by norm_num, show 1+2*(295057098043189973/50000000000000000000 : ℝ)=(25295057098043189973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34883199619526509927/34883750000000000000 : ℝ)*(X 1 0+X 2 0)+(911226065227/174418750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (151/100000 : ℝ)) (hi := (14029/50000 : ℝ)) (c := (34883199619526509927/34883750000000000000 : ℝ)) (alpha := (911226065227/174418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34883199619526509927/34883750000000000000 : ℝ)*(X 0 1+X 2 1)+(911226065227/174418750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (151/100000 : ℝ)) (hi := (14029/50000 : ℝ)) (c := (34883199619526509927/34883750000000000000 : ℝ)) (alpha := (911226065227/174418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34883199619526509927/34883750000000000000 : ℝ)*(X 0 2+X 1 2)+(911226065227/174418750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (151/100000 : ℝ)) (hi := (14029/50000 : ℝ)) (c := (34883199619526509927/34883750000000000000 : ℝ)) (alpha := (911226065227/174418750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212111847/1000000000 : ℝ)*X 0 0+(5718679459/10000000000 : ℝ)*X 0 1+(4988811243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422590713/10000000000 : ℝ)*X 1 0+(-2516286749/10000000000 : ℝ)*X 1 1+(199552461/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5422591443/10000000000 : ℝ)*X 2 0+(4988810741/10000000000 : ℝ)*X 2 1+(-2516286791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270170419/625000000 : ℝ)*X 0 0+(1832534103/5000000000 : ℝ)*X 0 1+(5099199393/10000000000 : ℝ)*X 0 2+(270170419/625000000 : ℝ)*X 1 0+(1832534103/5000000000 : ℝ)*X 1 1+(5099199393/10000000000 : ℝ)*X 1 2+(270170419/625000000 : ℝ)*X 2 0+(1832534103/5000000000 : ℝ)*X 2 1+(5099199393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122016951/10000000000 : ℝ)*X 0 0+(2499509367/5000000000 : ℝ)*X 0 1+(5708265673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047213447/2000000000 : ℝ)*X 1 0+(-56151013/312500000 : ℝ)*X 1 1+(570826553/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236067251/10000000000 : ℝ)*X 2 0+(5708265641/10000000000 : ℝ)*X 2 1+(-179683223/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108112289/250000000 : ℝ)*X 0 0+(5079143281/10000000000 : ℝ)*X 0 1+(3685529787/10000000000 : ℝ)*X 0 2+(108112289/250000000 : ℝ)*X 1 0+(5079143281/10000000000 : ℝ)*X 1 1+(3685529787/10000000000 : ℝ)*X 1 2+(108112289/250000000 : ℝ)*X 2 0+(5079143281/10000000000 : ℝ)*X 2 1+(3685529787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2681438992356499881956552679/1744187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85878641/100000000000000 : ℝ)*(base1) + (134984389/50000000000000 : ℝ)*(base19) + (28401003/6250000000000 : ℝ)*(base23) + (5632199/50000000000000 : ℝ)*(upper3) + (46947227/100000000000000 : ℝ)*(upper5) + (1033699894744841/100000000000000 : ℝ)*(major0) + (1033699894744841/100000000000000 : ℝ)*(major1) + (1033699894744841/100000000000000 : ℝ)*(major2) + (685055639184239/50000000000000 : ℝ)*(sp0) + (342528146973503/25000000000000 : ℝ)*(sp1) + (685056201723371/50000000000000 : ℝ)*(sp2) + (697286515825363/100000000000000 : ℝ)*(sp3) + (208171619/12500000000000 : ℝ)*(sp4) + (55735529/20000000000000 : ℝ)*(sp7) + (43580430023853/6250000000000 : ℝ)*(f.failure) + (137011285786279/10000000000000 : ℝ)*(f.sum) + (13074250415403/34883750000000000000000000000 : ℝ)*base65 + (36625192972693561607/3488375000000000000000000000000000 : ℝ)*base67 + (5369445270483563393/3488375000000000000000000000000000 : ℝ)*base70 + (7501649697280436607/3488375000000000000000000000000000 : ℝ)*base71 + (503965755493787/139535000000000000000000000000 : ℝ)*base73 + (12892521714127313393/3488375000000000000000000000000000 : ℝ)*base76 + (3399606220774186607/3488375000000000000000000000000000 : ℝ)*base77 + (3156050016648061607/3488375000000000000000000000000000 : ℝ)*base79 + (42025582912351/17441875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2229853/312500000000000000000 : ℝ)*base90 + (2229853/312500000000000000000 : ℝ)*base92 + (2229853/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11919247887492136257117539997/1744187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80763197/100000000000000 : ℝ)*(base1) + (153167527/10000000000000 : ℝ)*(base19) + (193642233/12500000000000 : ℝ)*(base23) + (155891427/100000000000000 : ℝ)*(upper3) + (7751261/5000000000000 : ℝ)*(upper5) + (1063752760396621/100000000000000 : ℝ)*(major0) + (1063752760396621/100000000000000 : ℝ)*(major1) + (1063752760396621/100000000000000 : ℝ)*(major2) + (6049016589/100000000000000 : ℝ)*(sp1) + (3209127477/50000000000000 : ℝ)*(sp2) + (1409946198646949/100000000000000 : ℝ)*(sp4) + (1409938537191893/100000000000000 : ℝ)*(sp5) + (704969075245467/50000000000000 : ℝ)*(sp6) + (143511818871281/20000000000000 : ℝ)*(sp7) + (717559175119601/100000000000000 : ℝ)*(f.failure) + (176243264735469/12500000000000 : ℝ)*(f.sum) + (73689935447563/139535000000000000000000000000 : ℝ)*base66 + (10614635214195031667/3488375000000000000000000000000000 : ℝ)*base67 + (612731387421656667/3488375000000000000000000000000000 : ℝ)*base69 + (17269414337746656667/3488375000000000000000000000000000 : ℝ)*base71 + (12052907057503/34883750000000000000000000000 : ℝ)*base73 + (28855121766913406667/3488375000000000000000000000000000 : ℝ)*base75 + (5048599814208156667/3488375000000000000000000000000000 : ℝ)*base77 + (26930054477808281667/3488375000000000000000000000000000 : ℝ)*base79 + (583719802332563/139535000000000000000000000000 : ℝ)*base82 + (40196601/5000000000000000000000 : ℝ)*base90 + (40196601/5000000000000000000000 : ℝ)*base92 + (40196601/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1079_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (529/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s2_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177801501/10000000000 : ℝ)*x 0 + (138080611/250000000 : ℝ)*x 1 + (643536297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177801501/10000000000 : ℝ)^517 ≤ (13188456700559/100000000000000 : ℝ)^389 := by
    have hnat : (2177801501 : ℕ)^517*100000000000000^389 ≤ 13188456700559^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177801501 10000000000 13188456700559 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138080611/250000000 : ℝ)^517 ≤ (11357990561771/25000000000000 : ℝ)^389 := by
    have hnat : (138080611 : ℕ)^517*25000000000000^389 ≤ 11357990561771^389*250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138080611 250000000 11357990561771 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643536297/1250000000 : ℝ)^517 ≤ (1655183241301/4000000000000 : ℝ)^389 := by
    have hnat : (643536297 : ℕ)^517*4000000000000^389 ≤ 1655183241301^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643536297 1250000000 1655183241301 4000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177801501/10000000000 : ℝ), (138080611/250000000 : ℝ), (643536297/1250000000 : ℝ)] ![(13188456700559/100000000000000 : ℝ), (11357990561771/25000000000000 : ℝ), (1655183241301/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177801501/10000000000 : ℝ)|^517 ≤ (13188456700559/100000000000000 : ℝ)^389
        have hw : |(-2177801501/10000000000 : ℝ)|=(2177801501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138080611/250000000 : ℝ)|^517 ≤ (11357990561771/25000000000000 : ℝ)^389
        have hw : |(138080611/250000000 : ℝ)|=(138080611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643536297/1250000000 : ℝ)|^517 ≤ (1655183241301/4000000000000 : ℝ)^389
        have hw : |(643536297/1250000000 : ℝ)|=(643536297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (107532413/200000000 : ℝ)*x 0 + (-237322741/1000000000 : ℝ)*x 1 + (5148290859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107532413/200000000 : ℝ)^517 ≤ (10959073326659/25000000000000 : ℝ)^389 := by
    have hnat : (107532413 : ℕ)^517*25000000000000^389 ≤ 10959073326659^389*200000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107532413 200000000 10959073326659 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237322741/1000000000 : ℝ)^517 ≤ (184801506071/1250000000000 : ℝ)^389 := by
    have hnat : (237322741 : ℕ)^517*1250000000000^389 ≤ 184801506071^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237322741 1000000000 184801506071 1250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148290859/10000000000 : ℝ)^517 ≤ (20689793096033/50000000000000 : ℝ)^389 := by
    have hnat : (5148290859 : ℕ)^517*50000000000000^389 ≤ 20689793096033^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148290859 10000000000 20689793096033 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107532413/200000000 : ℝ), (-237322741/1000000000 : ℝ), (5148290859/10000000000 : ℝ)] ![(10959073326659/25000000000000 : ℝ), (184801506071/1250000000000 : ℝ), (20689793096033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107532413/200000000 : ℝ)|^517 ≤ (10959073326659/25000000000000 : ℝ)^389
        have hw : |(107532413/200000000 : ℝ)|=(107532413/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237322741/1000000000 : ℝ)|^517 ≤ (184801506071/1250000000000 : ℝ)^389
        have hw : |(-237322741/1000000000 : ℝ)|=(237322741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148290859/10000000000 : ℝ)|^517 ≤ (20689793096033/50000000000000 : ℝ)^389
        have hw : |(5148290859/10000000000 : ℝ)|=(5148290859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5376620817/10000000000 : ℝ)*x 0 + (128707267/250000000 : ℝ)*x 1 + (-2373227423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376620817/10000000000 : ℝ)^517 ≤ (43836295116233/100000000000000 : ℝ)^389 := by
    have hnat : (5376620817 : ℕ)^517*100000000000000^389 ≤ 43836295116233^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376620817 10000000000 43836295116233 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128707267/250000000 : ℝ)^517 ≤ (20689792139969/50000000000000 : ℝ)^389 := by
    have hnat : (128707267 : ℕ)^517*50000000000000^389 ≤ 20689792139969^389*250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128707267 250000000 20689792139969 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373227423/10000000000 : ℝ)^517 ≤ (462003768541/3125000000000 : ℝ)^389 := by
    have hnat : (2373227423 : ℕ)^517*3125000000000^389 ≤ 462003768541^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373227423 10000000000 462003768541 3125000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376620817/10000000000 : ℝ), (128707267/250000000 : ℝ), (-2373227423/10000000000 : ℝ)] ![(43836295116233/100000000000000 : ℝ), (20689792139969/50000000000000 : ℝ), (462003768541/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376620817/10000000000 : ℝ)|^517 ≤ (43836295116233/100000000000000 : ℝ)^389
        have hw : |(5376620817/10000000000 : ℝ)|=(5376620817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128707267/250000000 : ℝ)|^517 ≤ (20689792139969/50000000000000 : ℝ)^389
        have hw : |(128707267/250000000 : ℝ)|=(128707267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2373227423/10000000000 : ℝ)|^517 ≤ (462003768541/3125000000000 : ℝ)^389
        have hw : |(-2373227423/10000000000 : ℝ)|=(2373227423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (87228891/200000000 : ℝ)*x 0 + (2004363433/5000000000 : ℝ)*x 1 + (4745441367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87228891/200000000 : ℝ)^517 ≤ (33193354234069/100000000000000 : ℝ)^389 := by
    have hnat : (87228891 : ℕ)^517*100000000000000^389 ≤ 33193354234069^389*200000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87228891 200000000 33193354234069 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004363433/5000000000 : ℝ)^517 ≤ (14837003806597/50000000000000 : ℝ)^389 := by
    have hnat : (2004363433 : ℕ)^517*50000000000000^389 ≤ 14837003806597^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004363433 5000000000 14837003806597 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4745441367/10000000000 : ℝ)^517 ≤ (37132638139167/100000000000000 : ℝ)^389 := by
    have hnat : (4745441367 : ℕ)^517*100000000000000^389 ≤ 37132638139167^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745441367 10000000000 37132638139167 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87228891/200000000 : ℝ), (2004363433/5000000000 : ℝ), (4745441367/10000000000 : ℝ)] ![(33193354234069/100000000000000 : ℝ), (14837003806597/50000000000000 : ℝ), (37132638139167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87228891/200000000 : ℝ)|^517 ≤ (33193354234069/100000000000000 : ℝ)^389
        have hw : |(87228891/200000000 : ℝ)|=(87228891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004363433/5000000000 : ℝ)|^517 ≤ (14837003806597/50000000000000 : ℝ)^389
        have hw : |(2004363433/5000000000 : ℝ)|=(2004363433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4745441367/10000000000 : ℝ)|^517 ≤ (37132638139167/100000000000000 : ℝ)^389
        have hw : |(4745441367/10000000000 : ℝ)|=(4745441367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-21779231/100000000 : ℝ)*x 0 + (5150992673/10000000000 : ℝ)*x 1 + (5520493959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21779231/100000000 : ℝ)^517 ≤ (13189435402883/100000000000000 : ℝ)^389 := by
    have hnat : (21779231 : ℕ)^517*100000000000000^389 ≤ 13189435402883^389*100000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21779231 100000000 13189435402883 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150992673/10000000000 : ℝ)^517 ≤ (5176056277613/12500000000000 : ℝ)^389 := by
    have hnat : (5150992673 : ℕ)^517*12500000000000^389 ≤ 5176056277613^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150992673 10000000000 5176056277613 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520493959/10000000000 : ℝ)^517 ≤ (2270105718061/5000000000000 : ℝ)^389 := by
    have hnat : (5520493959 : ℕ)^517*5000000000000^389 ≤ 2270105718061^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520493959 10000000000 2270105718061 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21779231/100000000 : ℝ), (5150992673/10000000000 : ℝ), (5520493959/10000000000 : ℝ)] ![(13189435402883/100000000000000 : ℝ), (5176056277613/12500000000000 : ℝ), (2270105718061/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21779231/100000000 : ℝ)|^517 ≤ (13189435402883/100000000000000 : ℝ)^389
        have hw : |(-21779231/100000000 : ℝ)|=(21779231/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150992673/10000000000 : ℝ)|^517 ≤ (5176056277613/12500000000000 : ℝ)^389
        have hw : |(5150992673/10000000000 : ℝ)|=(5150992673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520493959/10000000000 : ℝ)|^517 ≤ (2270105718061/5000000000000 : ℝ)^389
        have hw : |(5520493959/10000000000 : ℝ)|=(5520493959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5281897323/10000000000 : ℝ)*x 0 + (-400204847/2000000000 : ℝ)*x 1 + (2760247027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281897323/10000000000 : ℝ)^517 ≤ (42812866805821/100000000000000 : ℝ)^389 := by
    have hnat : (5281897323 : ℕ)^517*100000000000000^389 ≤ 42812866805821^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281897323 10000000000 42812866805821 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400204847/2000000000 : ℝ)^517 ≤ (1178501778177/10000000000000 : ℝ)^389 := by
    have hnat : (400204847 : ℕ)^517*10000000000000^389 ≤ 1178501778177^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400204847 2000000000 1178501778177 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760247027/5000000000 : ℝ)^517 ≤ (9080423079923/20000000000000 : ℝ)^389 := by
    have hnat : (2760247027 : ℕ)^517*20000000000000^389 ≤ 9080423079923^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760247027 5000000000 9080423079923 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281897323/10000000000 : ℝ), (-400204847/2000000000 : ℝ), (2760247027/5000000000 : ℝ)] ![(42812866805821/100000000000000 : ℝ), (1178501778177/10000000000000 : ℝ), (9080423079923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281897323/10000000000 : ℝ)|^517 ≤ (42812866805821/100000000000000 : ℝ)^389
        have hw : |(5281897323/10000000000 : ℝ)|=(5281897323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400204847/2000000000 : ℝ)|^517 ≤ (1178501778177/10000000000000 : ℝ)^389
        have hw : |(-400204847/2000000000 : ℝ)|=(400204847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760247027/5000000000 : ℝ)|^517 ≤ (9080423079923/20000000000000 : ℝ)^389
        have hw : |(2760247027/5000000000 : ℝ)|=(2760247027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2640948781/5000000000 : ℝ)*x 0 + (5520493897/10000000000 : ℝ)*x 1 + (-16008193/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640948781/5000000000 : ℝ)^517 ≤ (42812869380501/100000000000000 : ℝ)^389 := by
    have hnat : (2640948781 : ℕ)^517*100000000000000^389 ≤ 42812869380501^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640948781 5000000000 42812869380501 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520493897/10000000000 : ℝ)^517 ≤ (4540211368353/10000000000000 : ℝ)^389 := by
    have hnat : (5520493897 : ℕ)^517*10000000000000^389 ≤ 4540211368353^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520493897 10000000000 4540211368353 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16008193/80000000 : ℝ)^517 ≤ (11785016920753/100000000000000 : ℝ)^389 := by
    have hnat : (16008193 : ℕ)^517*100000000000000^389 ≤ 11785016920753^389*80000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16008193 80000000 11785016920753 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640948781/5000000000 : ℝ), (5520493897/10000000000 : ℝ), (-16008193/80000000 : ℝ)] ![(42812869380501/100000000000000 : ℝ), (4540211368353/10000000000000 : ℝ), (11785016920753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640948781/5000000000 : ℝ)|^517 ≤ (42812869380501/100000000000000 : ℝ)^389
        have hw : |(2640948781/5000000000 : ℝ)|=(2640948781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520493897/10000000000 : ℝ)|^517 ≤ (4540211368353/10000000000000 : ℝ)^389
        have hw : |(5520493897/10000000000 : ℝ)|=(5520493897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16008193/80000000 : ℝ)|^517 ≤ (11785016920753/100000000000000 : ℝ)^389
        have hw : |(-16008193/80000000 : ℝ)|=(16008193/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s2_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2180841811/5000000000 : ℝ)*x 0 + (592516509/1250000000 : ℝ)*x 1 + (4014091221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180841811/5000000000 : ℝ)^517 ≤ (33195772445993/100000000000000 : ℝ)^389 := by
    have hnat : (2180841811 : ℕ)^517*100000000000000^389 ≤ 33195772445993^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180841811 5000000000 33195772445993 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592516509/1250000000 : ℝ)^517 ≤ (741548666321/2000000000000 : ℝ)^389 := by
    have hnat : (592516509 : ℕ)^517*2000000000000^389 ≤ 741548666321^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592516509 1250000000 741548666321 2000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014091221/10000000000 : ℝ)^517 ≤ (7431698555593/25000000000000 : ℝ)^389 := by
    have hnat : (4014091221 : ℕ)^517*25000000000000^389 ≤ 7431698555593^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014091221 10000000000 7431698555593 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180841811/5000000000 : ℝ), (592516509/1250000000 : ℝ), (4014091221/10000000000 : ℝ)] ![(33195772445993/100000000000000 : ℝ), (741548666321/2000000000000 : ℝ), (7431698555593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180841811/5000000000 : ℝ)|^517 ≤ (33195772445993/100000000000000 : ℝ)^389
        have hw : |(2180841811/5000000000 : ℝ)|=(2180841811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(592516509/1250000000 : ℝ)|^517 ≤ (741548666321/2000000000000 : ℝ)^389
        have hw : |(592516509/1250000000 : ℝ)|=(592516509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014091221/10000000000 : ℝ)|^517 ≤ (7431698555593/25000000000000 : ℝ)^389
        have hw : |(4014091221/10000000000 : ℝ)|=(4014091221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (351/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8349/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (529/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (529/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (529/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (529/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (529/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (529/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (529/10000 : ℝ) ^ (8271/2048 : ℝ) ≤ (174791776625733/25000000000000000000 : ℝ) := by
    have hpowers : (529/10000 : ℝ)^8271 ≤ (174791776625733/25000000000000000000 : ℝ)^2048 := by
      have hnat : (529 : ℕ)^8271*25000000000000000000^2048 ≤ 174791776625733^2048*10000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        529 10000 174791776625733 25000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (529/10000 : ℝ)) (X := (174791776625733/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20729/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (173760456947513277/100000000000000000000 : ℝ) := by
    have hpowers : (20729/100000 : ℝ)^8271 ≤ (173760456947513277/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20729 : ℕ)^8271*100000000000000000000^2048 ≤ 173760456947513277^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20729 100000 173760456947513277 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20729/100000 : ℝ)) (X := (173760456947513277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500174791776625733/12500000000000000000 : ℝ) ≤ (5000017312135193/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (12500174791776625733/12500000000000000000 : ℝ)^2048 ≤ (5000017312135193/5000000000000000 : ℝ)^8271 := by
      have hnat : (12500174791776625733 : ℕ)^2048*5000000000000000^8271 ≤ 5000017312135193^8271*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500174791776625733 12500000000000000000 5000017312135193 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000017312135193/5000000000000000 : ℝ)) (X := (12500174791776625733/12500000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100174459624054016209/100000000000000000000 : ℝ) ≤ (5002158499908197/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100174459624054016209/100000000000000000000 : ℝ)^2048 ≤ (5002158499908197/5000000000000000 : ℝ)^8271 := by
      have hnat : (100174459624054016209 : ℕ)^2048*5000000000000000^8271 ≤ 5002158499908197^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100174459624054016209 100000000000000000000 5002158499908197 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002158499908197/5000000000000000 : ℝ)) (X := (100174459624054016209/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50173760456947513277/50000000000000000000 : ℝ) ≤ (5004299687681201/5000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50173760456947513277/50000000000000000000 : ℝ)^2048 ≤ (5004299687681201/5000000000000000 : ℝ)^8271 := by
      have hnat : (50173760456947513277 : ℕ)^2048*5000000000000000^8271 ≤ 5004299687681201^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50173760456947513277 50000000000000000000 5004299687681201 5000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004299687681201/5000000000000000 : ℝ)) (X := (50173760456947513277/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174791776625733/25000000000000000000 : ℝ) ≤ ((77172613515416862407/77195000000000000000 : ℝ)+2*(535296943251/192987500000000 : ℝ)*(529/10000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (77172613515416862407/77195000000000000000 : ℝ)+2*(535296943251/192987500000000 : ℝ)*(529/10000 : ℝ)=(5000017312135193/5000000000000000 : ℝ) by norm_num, show 1+2*(174791776625733/25000000000000000000 : ℝ)=(12500174791776625733/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(173760456947513277/100000000000000000000 : ℝ)+(174791776625733/25000000000000000000 : ℝ) ≤ ((77172613515416862407/77195000000000000000 : ℝ)+(535296943251/192987500000000 : ℝ)*((20729/100000 : ℝ)+(529/10000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (77172613515416862407/77195000000000000000 : ℝ)+(535296943251/192987500000000 : ℝ)*((20729/100000 : ℝ)+(529/10000 : ℝ))=(5002158499908197/5000000000000000 : ℝ) by norm_num, show 1+(173760456947513277/100000000000000000000 : ℝ)+(174791776625733/25000000000000000000 : ℝ)=(100174459624054016209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(173760456947513277/100000000000000000000 : ℝ) ≤ ((77172613515416862407/77195000000000000000 : ℝ)+2*(535296943251/192987500000000 : ℝ)*(20729/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (77172613515416862407/77195000000000000000 : ℝ)+2*(535296943251/192987500000000 : ℝ)*(20729/100000 : ℝ)=(5004299687681201/5000000000000000 : ℝ) by norm_num, show 1+2*(173760456947513277/100000000000000000000 : ℝ)=(50173760456947513277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77172613515416862407/77195000000000000000 : ℝ)*(X 1 0+X 2 0)+(535296943251/192987500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (529/10000 : ℝ)) (hi := (20729/100000 : ℝ)) (c := (77172613515416862407/77195000000000000000 : ℝ)) (alpha := (535296943251/192987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77172613515416862407/77195000000000000000 : ℝ)*(X 0 1+X 2 1)+(535296943251/192987500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (529/10000 : ℝ)) (hi := (20729/100000 : ℝ)) (c := (77172613515416862407/77195000000000000000 : ℝ)) (alpha := (535296943251/192987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77172613515416862407/77195000000000000000 : ℝ)*(X 0 2+X 1 2)+(535296943251/192987500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (529/10000 : ℝ)) (hi := (20729/100000 : ℝ)) (c := (77172613515416862407/77195000000000000000 : ℝ)) (alpha := (535296943251/192987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177801501/10000000000 : ℝ)*X 0 0+(138080611/250000000 : ℝ)*X 0 1+(643536297/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107532413/200000000 : ℝ)*X 1 0+(-237322741/1000000000 : ℝ)*X 1 1+(5148290859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376620817/10000000000 : ℝ)*X 2 0+(128707267/250000000 : ℝ)*X 2 1+(-2373227423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87228891/200000000 : ℝ)*X 0 0+(2004363433/5000000000 : ℝ)*X 0 1+(4745441367/10000000000 : ℝ)*X 0 2+(87228891/200000000 : ℝ)*X 1 0+(2004363433/5000000000 : ℝ)*X 1 1+(4745441367/10000000000 : ℝ)*X 1 2+(87228891/200000000 : ℝ)*X 2 0+(2004363433/5000000000 : ℝ)*X 2 1+(4745441367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21779231/100000000 : ℝ)*X 0 0+(5150992673/10000000000 : ℝ)*X 0 1+(5520493959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281897323/10000000000 : ℝ)*X 1 0+(-400204847/2000000000 : ℝ)*X 1 1+(2760247027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640948781/5000000000 : ℝ)*X 2 0+(5520493897/10000000000 : ℝ)*X 2 1+(-16008193/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180841811/5000000000 : ℝ)*X 0 0+(592516509/1250000000 : ℝ)*X 0 1+(4014091221/10000000000 : ℝ)*X 0 2+(2180841811/5000000000 : ℝ)*X 1 0+(592516509/1250000000 : ℝ)*X 1 1+(4014091221/10000000000 : ℝ)*X 1 2+(2180841811/5000000000 : ℝ)*X 2 0+(592516509/1250000000 : ℝ)*X 2 1+(4014091221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33424234279069526617319520891/3859750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9769517/20000000000000 : ℝ)*(base1) + (1611005499/100000000000000 : ℝ)*(base19) + (52932779/3125000000000 : ℝ)*(base23) + (33133191/20000000000000 : ℝ)*(upper3) + (88285257/50000000000000 : ℝ)*(upper5) + (2012284695545729/100000000000000 : ℝ)*(major0) + (2012284695545729/100000000000000 : ℝ)*(major1) + (2012284695545729/100000000000000 : ℝ)*(major2) + (66678854728581/2500000000000 : ℝ)*(sp0) + (1333585931711873/50000000000000 : ℝ)*(sp1) + (2667171780580317/100000000000000 : ℝ)*(sp2) + (84836665690263/6250000000000 : ℝ)*(sp3) + (1933413359/10000000000000 : ℝ)*(sp4) + (8928114117/100000000000000 : ℝ)*(sp7) + (135739562800591/10000000000000 : ℝ)*(f.failure) + (666793368607311/25000000000000 : ℝ)*(f.sum) + (35983326712351/38597500000000000000000000000 : ℝ)*base65 + (23701558978032109703/7719500000000000000000000000000000 : ℝ)*base67 + (33796843013922609703/7719500000000000000000000000000000 : ℝ)*base69 + (7694333414981890297/7719500000000000000000000000000000 : ℝ)*base72 + (28697668887723/19298750000000000000000000000 : ℝ)*base73 + (66960611944224609703/7719500000000000000000000000000000 : ℝ)*base75 + (21032210369982609703/7719500000000000000000000000000000 : ℝ)*base77 + (9342331165822890297/7719500000000000000000000000000000 : ℝ)*base80 + (181389366127971/38597500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1107591/500000000000000000000 : ℝ)*base90 + (1107591/500000000000000000000 : ℝ)*base92 + (1107591/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3833292822236848063985836323/964937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761730013/100000000000000 : ℝ)*(base19) + (475770069/50000000000000 : ℝ)*(base23) + (12319989/10000000000000 : ℝ)*(upper3) + (4181947/25000000000000 : ℝ)*(lower4) + (74372453/100000000000000 : ℝ)*(upper5) + (510460468019037/25000000000000 : ℝ)*(major0) + (510460468019037/25000000000000 : ℝ)*(major1) + (510460468019037/25000000000000 : ℝ)*(major2) + (261929883/4000000000000 : ℝ)*(sp1) + (8537861387/100000000000000 : ℝ)*(sp2) + (676587514574887/25000000000000 : ℝ)*(sp4) + (135317137416123/5000000000000 : ℝ)*(sp5) + (1353170284449011/50000000000000 : ℝ)*(sp6) + (17216669417917/1250000000000 : ℝ)*(sp7) + (17216669417917/1250000000000 : ℝ)*(f.failure) + (676587514574887/25000000000000 : ℝ)*(f.sum) + (3410400081799/4824687500000000000000000000 : ℝ)*base65 + (16728737514395942059/1929875000000000000000000000000000 : ℝ)*base67 + (5083345374673057941/1929875000000000000000000000000000 : ℝ)*base70 + (804889999593307941/1929875000000000000000000000000000 : ℝ)*base72 + (193950797151767/38597500000000000000000000000 : ℝ)*base73 + (4461411616853567059/1929875000000000000000000000000000 : ℝ)*base75 + (13724671434593317059/1929875000000000000000000000000000 : ℝ)*base77 + (17301653542332192059/1929875000000000000000000000000000 : ℝ)*base79 + (317889051517071/77195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (126917/62500000000000000000 : ℝ)*base90 + (126917/62500000000000000000 : ℝ)*base92 + (126917/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (529/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1079_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1079_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1079_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1079_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
