-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:38.583794+00:00
-- url     : https://prove2.me/submissions/e0cf48d3-d238-41f7-bdf6-38a6e1bd720c

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
theorem support_rectangle_w1204_s3_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067203269/5000000000 : ℝ)*x 0 + (5423094061/10000000000 : ℝ)*x 1 + (1047515477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067203269/5000000000 : ℝ)^8397 ≤ (405295486919/3125000000000 : ℝ)^6349 := by
    have hnat : (1067203269 : ℕ)^8397*3125000000000^6349 ≤ 405295486919^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067203269 5000000000 405295486919 3125000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423094061/10000000000 : ℝ)^8397 ≤ (44516714845141/100000000000000 : ℝ)^6349 := by
    have hnat : (5423094061 : ℕ)^8397*100000000000000^6349 ≤ 44516714845141^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423094061 10000000000 44516714845141 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047515477/2000000000 : ℝ)^8397 ≤ (5314228694059/12500000000000 : ℝ)^6349 := by
    have hnat : (1047515477 : ℕ)^8397*12500000000000^6349 ≤ 5314228694059^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047515477 2000000000 5314228694059 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067203269/5000000000 : ℝ), (5423094061/10000000000 : ℝ), (1047515477/2000000000 : ℝ)] ![(405295486919/3125000000000 : ℝ), (44516714845141/100000000000000 : ℝ), (5314228694059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067203269/5000000000 : ℝ)|^8397 ≤ (405295486919/3125000000000 : ℝ)^6349
        have hw : |(-1067203269/5000000000 : ℝ)|=(1067203269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423094061/10000000000 : ℝ)|^8397 ≤ (44516714845141/100000000000000 : ℝ)^6349
        have hw : |(5423094061/10000000000 : ℝ)|=(5423094061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047515477/2000000000 : ℝ)|^8397 ≤ (5314228694059/12500000000000 : ℝ)^6349
        have hw : |(1047515477/2000000000 : ℝ)|=(1047515477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334521401/625000000 : ℝ)*x 0 + (-11145571/50000000 : ℝ)*x 1 + (2618788583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334521401/625000000 : ℝ)^8397 ≤ (43750211901971/100000000000000 : ℝ)^6349 := by
    have hnat : (334521401 : ℕ)^8397*100000000000000^6349 ≤ 43750211901971^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334521401 625000000 43750211901971 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11145571/50000000 : ℝ)^8397 ≤ (6867980438571/50000000000000 : ℝ)^6349 := by
    have hnat : (11145571 : ℕ)^8397*50000000000000^6349 ≤ 6867980438571^6349*50000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11145571 50000000 6867980438571 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618788583/5000000000 : ℝ)^8397 ≤ (21256913600709/50000000000000 : ℝ)^6349 := by
    have hnat : (2618788583 : ℕ)^8397*50000000000000^6349 ≤ 21256913600709^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618788583 5000000000 21256913600709 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334521401/625000000 : ℝ), (-11145571/50000000 : ℝ), (2618788583/5000000000 : ℝ)] ![(43750211901971/100000000000000 : ℝ), (6867980438571/50000000000000 : ℝ), (21256913600709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334521401/625000000 : ℝ)|^8397 ≤ (43750211901971/100000000000000 : ℝ)^6349
        have hw : |(334521401/625000000 : ℝ)|=(334521401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11145571/50000000 : ℝ)|^8397 ≤ (6867980438571/50000000000000 : ℝ)^6349
        have hw : |(-11145571/50000000 : ℝ)|=(11145571/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618788583/5000000000 : ℝ)|^8397 ≤ (21256913600709/50000000000000 : ℝ)^6349
        have hw : |(2618788583/5000000000 : ℝ)|=(2618788583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352342521/10000000000 : ℝ)*x 0 + (261878853/500000000 : ℝ)*x 1 + (-2229114201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352342521/10000000000 : ℝ)^8397 ≤ (21875106518549/50000000000000 : ℝ)^6349 := by
    have hnat : (5352342521 : ℕ)^8397*50000000000000^6349 ≤ 21875106518549^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352342521 10000000000 21875106518549 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261878853/500000000 : ℝ)^8397 ≤ (5314228257933/12500000000000 : ℝ)^6349 := by
    have hnat : (261878853 : ℕ)^8397*12500000000000^6349 ≤ 5314228257933^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261878853 500000000 5314228257933 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229114201/10000000000 : ℝ)^8397 ≤ (13735960885291/100000000000000 : ℝ)^6349 := by
    have hnat : (2229114201 : ℕ)^8397*100000000000000^6349 ≤ 13735960885291^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229114201 10000000000 13735960885291 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352342521/10000000000 : ℝ), (261878853/500000000 : ℝ), (-2229114201/10000000000 : ℝ)] ![(21875106518549/50000000000000 : ℝ), (5314228257933/12500000000000 : ℝ), (13735960885291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352342521/10000000000 : ℝ)|^8397 ≤ (21875106518549/50000000000000 : ℝ)^6349
        have hw : |(5352342521/10000000000 : ℝ)|=(5352342521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261878853/500000000 : ℝ)|^8397 ≤ (5314228257933/12500000000000 : ℝ)^6349
        have hw : |(261878853/500000000 : ℝ)|=(261878853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229114201/10000000000 : ℝ)|^8397 ≤ (13735960885291/100000000000000 : ℝ)^6349
        have hw : |(-2229114201/10000000000 : ℝ)|=(2229114201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177059357/5000000000 : ℝ)*x 0 + (4171256341/10000000000 : ℝ)*x 1 + (1136207739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177059357/5000000000 : ℝ)^8397 ≤ (8324538354303/25000000000000 : ℝ)^6349 := by
    have hnat : (2177059357 : ℕ)^8397*25000000000000^6349 ≤ 8324538354303^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177059357 5000000000 8324538354303 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171256341/10000000000 : ℝ)^8397 ≤ (3146126520701/10000000000000 : ℝ)^6349 := by
    have hnat : (4171256341 : ℕ)^8397*10000000000000^6349 ≤ 3146126520701^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171256341 10000000000 3146126520701 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136207739/2500000000 : ℝ)^8397 ≤ (8810145340679/25000000000000 : ℝ)^6349 := by
    have hnat : (1136207739 : ℕ)^8397*25000000000000^6349 ≤ 8810145340679^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136207739 2500000000 8810145340679 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177059357/5000000000 : ℝ), (4171256341/10000000000 : ℝ), (1136207739/2500000000 : ℝ)] ![(8324538354303/25000000000000 : ℝ), (3146126520701/10000000000000 : ℝ), (8810145340679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177059357/5000000000 : ℝ)|^8397 ≤ (8324538354303/25000000000000 : ℝ)^6349
        have hw : |(2177059357/5000000000 : ℝ)|=(2177059357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171256341/10000000000 : ℝ)|^8397 ≤ (3146126520701/10000000000000 : ℝ)^6349
        have hw : |(4171256341/10000000000 : ℝ)|=(4171256341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136207739/2500000000 : ℝ)|^8397 ≤ (8810145340679/25000000000000 : ℝ)^6349
        have hw : |(1136207739/2500000000 : ℝ)|=(1136207739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134422047/10000000000 : ℝ)*x 0 + (261913399/500000000 : ℝ)*x 1 + (1355599917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134422047/10000000000 : ℝ)^8397 ≤ (12969580218623/100000000000000 : ℝ)^6349 := by
    have hnat : (2134422047 : ℕ)^8397*100000000000000^6349 ≤ 12969580218623^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134422047 10000000000 12969580218623 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261913399/500000000 : ℝ)^8397 ≤ (42521243530003/100000000000000 : ℝ)^6349 := by
    have hnat : (261913399 : ℕ)^8397*100000000000000^6349 ≤ 42521243530003^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261913399 500000000 42521243530003 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355599917/2500000000 : ℝ)^8397 ≤ (44509176237131/100000000000000 : ℝ)^6349 := by
    have hnat : (1355599917 : ℕ)^8397*100000000000000^6349 ≤ 44509176237131^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355599917 2500000000 44509176237131 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134422047/10000000000 : ℝ), (261913399/500000000 : ℝ), (1355599917/2500000000 : ℝ)] ![(12969580218623/100000000000000 : ℝ), (42521243530003/100000000000000 : ℝ), (44509176237131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134422047/10000000000 : ℝ)|^8397 ≤ (12969580218623/100000000000000 : ℝ)^6349
        have hw : |(-2134422047/10000000000 : ℝ)|=(2134422047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261913399/500000000 : ℝ)|^8397 ≤ (42521243530003/100000000000000 : ℝ)^6349
        have hw : |(261913399/500000000 : ℝ)|=(261913399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355599917/2500000000 : ℝ)|^8397 ≤ (44509176237131/100000000000000 : ℝ)^6349
        have hw : |(1355599917/2500000000 : ℝ)|=(1355599917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305134399/10000000000 : ℝ)*x 0 + (-2044291879/10000000000 : ℝ)*x 1 + (216895999/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305134399/10000000000 : ℝ)^8397 ≤ (1729623445563/4000000000000 : ℝ)^6349 := by
    have hnat : (5305134399 : ℕ)^8397*4000000000000^6349 ≤ 1729623445563^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305134399 10000000000 1729623445563 4000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044291879/10000000000 : ℝ)^8397 ≤ (12250234277279/100000000000000 : ℝ)^6349 := by
    have hnat : (2044291879 : ℕ)^8397*100000000000000^6349 ≤ 12250234277279^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044291879 10000000000 12250234277279 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216895999/400000000 : ℝ)^8397 ≤ (44509179569977/100000000000000 : ℝ)^6349 := by
    have hnat : (216895999 : ℕ)^8397*100000000000000^6349 ≤ 44509179569977^6349*400000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216895999 400000000 44509179569977 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305134399/10000000000 : ℝ), (-2044291879/10000000000 : ℝ), (216895999/400000000 : ℝ)] ![(1729623445563/4000000000000 : ℝ), (12250234277279/100000000000000 : ℝ), (44509179569977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305134399/10000000000 : ℝ)|^8397 ≤ (1729623445563/4000000000000 : ℝ)^6349
        have hw : |(5305134399/10000000000 : ℝ)|=(5305134399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044291879/10000000000 : ℝ)|^8397 ≤ (12250234277279/100000000000000 : ℝ)^6349
        have hw : |(-2044291879/10000000000 : ℝ)|=(2044291879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216895999/400000000 : ℝ)|^8397 ≤ (44509179569977/100000000000000 : ℝ)^6349
        have hw : |(216895999/400000000 : ℝ)|=(216895999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652567791/5000000000 : ℝ)*x 0 + (1355599859/2500000000 : ℝ)*x 1 + (-31942047/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652567791/5000000000 : ℝ)^8397 ≤ (10810149722919/25000000000000 : ℝ)^6349 := by
    have hnat : (2652567791 : ℕ)^8397*25000000000000^6349 ≤ 10810149722919^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652567791 5000000000 10810149722919 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355599859/2500000000 : ℝ)^8397 ≤ (22254586859249/50000000000000 : ℝ)^6349 := by
    have hnat : (1355599859 : ℕ)^8397*50000000000000^6349 ≤ 22254586859249^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355599859 2500000000 22254586859249 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31942047/156250000 : ℝ)^8397 ≤ (1225022737427/10000000000000 : ℝ)^6349 := by
    have hnat : (31942047 : ℕ)^8397*10000000000000^6349 ≤ 1225022737427^6349*156250000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31942047 156250000 1225022737427 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652567791/5000000000 : ℝ), (1355599859/2500000000 : ℝ), (-31942047/156250000 : ℝ)] ![(10810149722919/25000000000000 : ℝ), (22254586859249/50000000000000 : ℝ), (1225022737427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652567791/5000000000 : ℝ)|^8397 ≤ (10810149722919/25000000000000 : ℝ)^6349
        have hw : |(2652567791/5000000000 : ℝ)|=(2652567791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355599859/2500000000 : ℝ)|^8397 ≤ (22254586859249/50000000000000 : ℝ)^6349
        have hw : |(1355599859/2500000000 : ℝ)|=(1355599859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31942047/156250000 : ℝ)|^8397 ≤ (1225022737427/10000000000000 : ℝ)^6349
        have hw : |(-31942047/156250000 : ℝ)|=(31942047/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s3_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088537429/2500000000 : ℝ)*x 0 + (283965053/625000000 : ℝ)*x 1 + (2086326933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088537429/2500000000 : ℝ)^8397 ≤ (33298466983179/100000000000000 : ℝ)^6349 := by
    have hnat : (1088537429 : ℕ)^8397*100000000000000^6349 ≤ 33298466983179^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088537429 2500000000 33298466983179 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283965053/625000000 : ℝ)^8397 ≤ (35226326229759/100000000000000 : ℝ)^6349 := by
    have hnat : (283965053 : ℕ)^8397*100000000000000^6349 ≤ 35226326229759^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283965053 625000000 35226326229759 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086326933/5000000000 : ℝ)^8397 ≤ (31475206760871/100000000000000 : ℝ)^6349 := by
    have hnat : (2086326933 : ℕ)^8397*100000000000000^6349 ≤ 31475206760871^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086326933 5000000000 31475206760871 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088537429/2500000000 : ℝ), (283965053/625000000 : ℝ), (2086326933/5000000000 : ℝ)] ![(33298466983179/100000000000000 : ℝ), (35226326229759/100000000000000 : ℝ), (31475206760871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088537429/2500000000 : ℝ)|^8397 ≤ (33298466983179/100000000000000 : ℝ)^6349
        have hw : |(1088537429/2500000000 : ℝ)|=(1088537429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283965053/625000000 : ℝ)|^8397 ≤ (35226326229759/100000000000000 : ℝ)^6349
        have hw : |(283965053/625000000 : ℝ)|=(283965053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086326933/5000000000 : ℝ)|^8397 ≤ (31475206760871/100000000000000 : ℝ)^6349
        have hw : |(2086326933/5000000000 : ℝ)|=(2086326933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10811/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (653/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (653/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (653/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (653/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (653/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (653/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4671/50000 : ℝ) ^ (2099/512 : ℝ) ≤ (3007292106552803/50000000000000000000 : ℝ) := by
    have hpowers : (4671/50000 : ℝ)^2099 ≤ (3007292106552803/50000000000000000000 : ℝ)^512 := by
      have hnat : (4671 : ℕ)^2099*50000000000000000000^512 ≤ 3007292106552803^512*50000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4671 50000 3007292106552803 50000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4671/50000 : ℝ)) (X := (3007292106552803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (653/4000 : ℝ) ^ (2099/512 : ℝ) ≤ (59293291275723461/100000000000000000000 : ℝ) := by
    have hpowers : (653/4000 : ℝ)^2099 ≤ (59293291275723461/100000000000000000000 : ℝ)^512 := by
      have hnat : (653 : ℕ)^2099*100000000000000000000^512 ≤ 59293291275723461^512*4000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        653 4000 59293291275723461 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (653/4000 : ℝ)) (X := (59293291275723461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003007292106552803/25000000000000000000 : ℝ) ≤ (10000293408965131/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25003007292106552803/25000000000000000000 : ℝ)^512 ≤ (10000293408965131/10000000000000000 : ℝ)^2099 := by
      have hnat : (25003007292106552803 : ℕ)^512*10000000000000000^2099 ≤ 10000293408965131^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003007292106552803 25000000000000000000 10000293408965131 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000293408965131/10000000000000000 : ℝ)) (X := (25003007292106552803/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100065307875488829067/100000000000000000000 : ℝ) ≤ (5000796316818803/5000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (100065307875488829067/100000000000000000000 : ℝ)^512 ≤ (5000796316818803/5000000000000000 : ℝ)^2099 := by
      have hnat : (100065307875488829067 : ℕ)^512*5000000000000000^2099 ≤ 5000796316818803^2099*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065307875488829067 100000000000000000000 5000796316818803 5000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000796316818803/5000000000000000 : ℝ)) (X := (100065307875488829067/100000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059293291275723461/50000000000000000000 : ℝ) ≤ (10002891858310081/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50059293291275723461/50000000000000000000 : ℝ)^512 ≤ (10002891858310081/10000000000000000 : ℝ)^2099 := by
      have hnat : (50059293291275723461 : ℕ)^512*10000000000000000^2099 ≤ 10002891858310081^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059293291275723461 50000000000000000000 10002891858310081 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002891858310081/10000000000000000 : ℝ)) (X := (50059293291275723461/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3007292106552803/50000000000000000000 : ℝ) ≤ ((69807774161022986873/69830000000000000000 : ℝ)+2*(51968986899/27932000000000 : ℝ)*(4671/50000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (69807774161022986873/69830000000000000000 : ℝ)+2*(51968986899/27932000000000 : ℝ)*(4671/50000 : ℝ)=(10000293408965131/10000000000000000 : ℝ) by norm_num, show 1+2*(3007292106552803/50000000000000000000 : ℝ)=(25003007292106552803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59293291275723461/100000000000000000000 : ℝ)+(3007292106552803/50000000000000000000 : ℝ) ≤ ((69807774161022986873/69830000000000000000 : ℝ)+(51968986899/27932000000000 : ℝ)*((653/4000 : ℝ)+(4671/50000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (69807774161022986873/69830000000000000000 : ℝ)+(51968986899/27932000000000 : ℝ)*((653/4000 : ℝ)+(4671/50000 : ℝ))=(5000796316818803/5000000000000000 : ℝ) by norm_num, show 1+(59293291275723461/100000000000000000000 : ℝ)+(3007292106552803/50000000000000000000 : ℝ)=(100065307875488829067/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59293291275723461/100000000000000000000 : ℝ) ≤ ((69807774161022986873/69830000000000000000 : ℝ)+2*(51968986899/27932000000000 : ℝ)*(653/4000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (69807774161022986873/69830000000000000000 : ℝ)+2*(51968986899/27932000000000 : ℝ)*(653/4000 : ℝ)=(10002891858310081/10000000000000000 : ℝ) by norm_num, show 1+2*(59293291275723461/100000000000000000000 : ℝ)=(50059293291275723461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69807774161022986873/69830000000000000000 : ℝ)*(X 1 0+X 2 0)+(51968986899/27932000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (4671/50000 : ℝ)) (hi := (653/4000 : ℝ)) (c := (69807774161022986873/69830000000000000000 : ℝ)) (alpha := (51968986899/27932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69807774161022986873/69830000000000000000 : ℝ)*(X 0 1+X 2 1)+(51968986899/27932000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (4671/50000 : ℝ)) (hi := (653/4000 : ℝ)) (c := (69807774161022986873/69830000000000000000 : ℝ)) (alpha := (51968986899/27932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69807774161022986873/69830000000000000000 : ℝ)*(X 0 2+X 1 2)+(51968986899/27932000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (4671/50000 : ℝ)) (hi := (653/4000 : ℝ)) (c := (69807774161022986873/69830000000000000000 : ℝ)) (alpha := (51968986899/27932000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067203269/5000000000 : ℝ)*X 0 0+(5423094061/10000000000 : ℝ)*X 0 1+(1047515477/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334521401/625000000 : ℝ)*X 1 0+(-11145571/50000000 : ℝ)*X 1 1+(2618788583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352342521/10000000000 : ℝ)*X 2 0+(261878853/500000000 : ℝ)*X 2 1+(-2229114201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177059357/5000000000 : ℝ)*X 0 0+(4171256341/10000000000 : ℝ)*X 0 1+(1136207739/2500000000 : ℝ)*X 0 2+(2177059357/5000000000 : ℝ)*X 1 0+(4171256341/10000000000 : ℝ)*X 1 1+(1136207739/2500000000 : ℝ)*X 1 2+(2177059357/5000000000 : ℝ)*X 2 0+(4171256341/10000000000 : ℝ)*X 2 1+(1136207739/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134422047/10000000000 : ℝ)*X 0 0+(261913399/500000000 : ℝ)*X 0 1+(1355599917/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305134399/10000000000 : ℝ)*X 1 0+(-2044291879/10000000000 : ℝ)*X 1 1+(216895999/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652567791/5000000000 : ℝ)*X 2 0+(1355599859/2500000000 : ℝ)*X 2 1+(-31942047/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088537429/2500000000 : ℝ)*X 0 0+(283965053/625000000 : ℝ)*X 0 1+(2086326933/5000000000 : ℝ)*X 0 2+(1088537429/2500000000 : ℝ)*X 1 0+(283965053/625000000 : ℝ)*X 1 1+(2086326933/5000000000 : ℝ)*X 1 2+(1088537429/2500000000 : ℝ)*X 2 0+(283965053/625000000 : ℝ)*X 2 1+(2086326933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2315518660331267547309134613/436437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5113407/390625000000 : ℝ)*(base19) + (134691231/10000000000000 : ℝ)*(base23) + (2270271/6250000000000 : ℝ)*(lower2) + (148703721/100000000000000 : ℝ)*(upper3) + (115480289/100000000000000 : ℝ)*(upper5) + (1008406494394127/25000000000000 : ℝ)*(major0) + (1008406494394127/25000000000000 : ℝ)*(major1) + (1008406494394127/25000000000000 : ℝ)*(major2) + (673796229617559/12500000000000 : ℝ)*(sp0) + (5390387825540059/100000000000000 : ℝ)*(sp1) + (2695193893829971/50000000000000 : ℝ)*(sp2) + (1338425717853389/50000000000000 : ℝ)*(sp3) + (964881589/5000000000000 : ℝ)*(sp4) + (5604012009/50000000000000 : ℝ)*(sp7) + (669215660932699/25000000000000 : ℝ)*(f.failure) + (5390389134572251/100000000000000 : ℝ)*(f.sum) + (230165505697/1745750000000000000000000000 : ℝ)*base65 + (11650070946103705129/1745750000000000000000000000000000 : ℝ)*base68 + (4491412241934794871/1745750000000000000000000000000000 : ℝ)*base69 + (3135798850631205129/1745750000000000000000000000000000 : ℝ)*base72 + (2266062550793/3491500000000000000000000000 : ℝ)*base74 + (2212299240920705129/1745750000000000000000000000000000 : ℝ)*base76 + (4466324374369705129/1745750000000000000000000000000000 : ℝ)*base78 + (43391278815459705129/1745750000000000000000000000000000 : ℝ)*base80 + (11905208837349/3491500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (378799/78125000000000000000 : ℝ)*base89 + (378799/78125000000000000000 : ℝ)*base91 + (378799/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1306679026263904470142410999/698300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82074693/20000000000000 : ℝ)*(base19) + (2061489307/100000000000000 : ℝ)*(base23) + (49737491/100000000000000 : ℝ)*(upper2) + (206882129/100000000000000 : ℝ)*(upper3) + (812787794565993/20000000000000 : ℝ)*(major0) + (812787794565993/20000000000000 : ℝ)*(major1) + (812787794565993/20000000000000 : ℝ)*(major2) + (3995692193/50000000000000 : ℝ)*(sp1) + (46910975697/100000000000000 : ℝ)*(sp2) + (636230051/25000000000000 : ℝ)*(sp3) + (543089842032949/10000000000000 : ℝ)*(sp4) + (5430890018571639/100000000000000 : ℝ)*(sp5) + (1086169889572897/20000000000000 : ℝ)*(sp6) + (1348488459017969/50000000000000 : ℝ)*(sp7) + (1348489731478071/50000000000000 : ℝ)*(f.failure) + (543089842032949/10000000000000 : ℝ)*(f.sum) + (13992811966347/6983000000000000000000000000 : ℝ)*base66 + (7325480055877909889/1396600000000000000000000000000000 : ℝ)*base67 + (6269173567255509889/1396600000000000000000000000000000 : ℝ)*base69 + (10866868544962109889/1396600000000000000000000000000000 : ℝ)*base71 + (5263165584253/3491500000000000000000000000 : ℝ)*base74 + (8133313655110909889/1396600000000000000000000000000000 : ℝ)*base75 + (3484872675920109889/1396600000000000000000000000000000 : ℝ)*base77 + (22441704341549909889/1396600000000000000000000000000000 : ℝ)*base79 + (2056885753729/698300000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (302529/156250000000000000000 : ℝ)*base90 + (302529/156250000000000000000 : ℝ)*base92 + (302529/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s4_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068474561/5000000000 : ℝ)*x 0 + (5399074947/10000000000 : ℝ)*x 1 + (5259931239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068474561/5000000000 : ℝ)^8397 ≤ (6494946408457/50000000000000 : ℝ)^6349 := by
    have hnat : (1068474561 : ℕ)^8397*50000000000000^6349 ≤ 6494946408457^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068474561 5000000000 6494946408457 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399074947/10000000000 : ℝ)^8397 ≤ (2766008426141/6250000000000 : ℝ)^6349 := by
    have hnat : (5399074947 : ℕ)^8397*6250000000000^6349 ≤ 2766008426141^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399074947 10000000000 2766008426141 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259931239/10000000000 : ℝ)^8397 ≤ (42753972353467/100000000000000 : ℝ)^6349 := by
    have hnat : (5259931239 : ℕ)^8397*100000000000000^6349 ≤ 42753972353467^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259931239 10000000000 42753972353467 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068474561/5000000000 : ℝ), (5399074947/10000000000 : ℝ), (5259931239/10000000000 : ℝ)] ![(6494946408457/50000000000000 : ℝ), (2766008426141/6250000000000 : ℝ), (42753972353467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068474561/5000000000 : ℝ)|^8397 ≤ (6494946408457/50000000000000 : ℝ)^6349
        have hw : |(-1068474561/5000000000 : ℝ)|=(1068474561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399074947/10000000000 : ℝ)|^8397 ≤ (2766008426141/6250000000000 : ℝ)^6349
        have hw : |(5399074947/10000000000 : ℝ)|=(5399074947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259931239/10000000000 : ℝ)|^8397 ≤ (42753972353467/100000000000000 : ℝ)^6349
        have hw : |(5259931239/10000000000 : ℝ)|=(5259931239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336576903/2500000000 : ℝ)*x 0 + (-137976117/625000000 : ℝ)*x 1 + (525993131/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336576903/2500000000 : ℝ)^8397 ≤ (10921245780223/25000000000000 : ℝ)^6349 := by
    have hnat : (1336576903 : ℕ)^8397*25000000000000^6349 ≤ 10921245780223^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336576903 2500000000 10921245780223 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137976117/625000000 : ℝ)^8397 ≤ (339026093603/2500000000000 : ℝ)^6349 := by
    have hnat : (137976117 : ℕ)^8397*2500000000000^6349 ≤ 339026093603^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137976117 625000000 339026093603 2500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525993131/1000000000 : ℝ)^8397 ≤ (42753973116729/100000000000000 : ℝ)^6349 := by
    have hnat : (525993131 : ℕ)^8397*100000000000000^6349 ≤ 42753973116729^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525993131 1000000000 42753973116729 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336576903/2500000000 : ℝ), (-137976117/625000000 : ℝ), (525993131/1000000000 : ℝ)] ![(10921245780223/25000000000000 : ℝ), (339026093603/2500000000000 : ℝ), (42753973116729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336576903/2500000000 : ℝ)|^8397 ≤ (10921245780223/25000000000000 : ℝ)^6349
        have hw : |(1336576903/2500000000 : ℝ)|=(1336576903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137976117/625000000 : ℝ)|^8397 ≤ (339026093603/2500000000000 : ℝ)^6349
        have hw : |(-137976117/625000000 : ℝ)|=(137976117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525993131/1000000000 : ℝ)|^8397 ≤ (42753973116729/100000000000000 : ℝ)^6349
        have hw : |(525993131/1000000000 : ℝ)|=(525993131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336576899/2500000000 : ℝ)*x 0 + (2629965627/5000000000 : ℝ)*x 1 + (-2207617967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336576899/2500000000 : ℝ)^8397 ≤ (2730311434249/6250000000000 : ℝ)^6349 := by
    have hnat : (1336576899 : ℕ)^8397*6250000000000^6349 ≤ 2730311434249^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336576899 2500000000 2730311434249 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629965627/5000000000 : ℝ)^8397 ≤ (267212328217/625000000000 : ℝ)^6349 := by
    have hnat : (2629965627 : ℕ)^8397*625000000000^6349 ≤ 267212328217^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629965627 5000000000 267212328217 625000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207617967/10000000000 : ℝ)^8397 ≤ (3390261128983/25000000000000 : ℝ)^6349 := by
    have hnat : (2207617967 : ℕ)^8397*25000000000000^6349 ≤ 3390261128983^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207617967 10000000000 3390261128983 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336576899/2500000000 : ℝ), (2629965627/5000000000 : ℝ), (-2207617967/10000000000 : ℝ)] ![(2730311434249/6250000000000 : ℝ), (267212328217/625000000000 : ℝ), (3390261128983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336576899/2500000000 : ℝ)|^8397 ≤ (2730311434249/6250000000000 : ℝ)^6349
        have hw : |(1336576899/2500000000 : ℝ)|=(1336576899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629965627/5000000000 : ℝ)|^8397 ≤ (267212328217/625000000000 : ℝ)^6349
        have hw : |(2629965627/5000000000 : ℝ)|=(2629965627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207617967/10000000000 : ℝ)|^8397 ≤ (3390261128983/25000000000000 : ℝ)^6349
        have hw : |(-2207617967/10000000000 : ℝ)|=(2207617967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355639211/10000000000 : ℝ)*x 0 + (4217751951/10000000000 : ℝ)*x 1 + (89958903/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355639211/10000000000 : ℝ)^8397 ≤ (33313533148077/100000000000000 : ℝ)^6349 := by
    have hnat : (4355639211 : ℕ)^8397*100000000000000^6349 ≤ 33313533148077^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355639211 10000000000 33313533148077 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217751951/10000000000 : ℝ)^8397 ≤ (31925906922121/100000000000000 : ℝ)^6349 := by
    have hnat : (4217751951 : ℕ)^8397*100000000000000^6349 ≤ 31925906922121^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217751951 10000000000 31925906922121 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89958903/200000000 : ℝ)^8397 ≤ (34760559918433/100000000000000 : ℝ)^6349 := by
    have hnat : (89958903 : ℕ)^8397*100000000000000^6349 ≤ 34760559918433^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89958903 200000000 34760559918433 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355639211/10000000000 : ℝ), (4217751951/10000000000 : ℝ), (89958903/200000000 : ℝ)] ![(33313533148077/100000000000000 : ℝ), (31925906922121/100000000000000 : ℝ), (34760559918433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355639211/10000000000 : ℝ)|^8397 ≤ (33313533148077/100000000000000 : ℝ)^6349
        have hw : |(4355639211/10000000000 : ℝ)|=(4355639211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217751951/10000000000 : ℝ)|^8397 ≤ (31925906922121/100000000000000 : ℝ)^6349
        have hw : |(4217751951/10000000000 : ℝ)|=(4217751951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89958903/200000000 : ℝ)|^8397 ≤ (34760559918433/100000000000000 : ℝ)^6349
        have hw : |(89958903/200000000 : ℝ)|=(89958903/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106847743/500000000 : ℝ)*x 0 + (526032021/1000000000 : ℝ)*x 1 + (5398684973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106847743/500000000 : ℝ)^8397 ≤ (12989938947709/100000000000000 : ℝ)^6349 := by
    have hnat : (106847743 : ℕ)^8397*100000000000000^6349 ≤ 12989938947709^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106847743 500000000 12989938947709 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526032021/1000000000 : ℝ)^8397 ≤ (5344769238343/12500000000000 : ℝ)^6349 := by
    have hnat : (526032021 : ℕ)^8397*12500000000000^6349 ≤ 5344769238343^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526032021 1000000000 5344769238343 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398684973/10000000000 : ℝ)^8397 ≤ (22125953562131/50000000000000 : ℝ)^6349 := by
    have hnat : (5398684973 : ℕ)^8397*50000000000000^6349 ≤ 22125953562131^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398684973 10000000000 22125953562131 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106847743/500000000 : ℝ), (526032021/1000000000 : ℝ), (5398684973/10000000000 : ℝ)] ![(12989938947709/100000000000000 : ℝ), (5344769238343/12500000000000 : ℝ), (22125953562131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106847743/500000000 : ℝ)|^8397 ≤ (12989938947709/100000000000000 : ℝ)^6349
        have hw : |(-106847743/500000000 : ℝ)|=(106847743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526032021/1000000000 : ℝ)|^8397 ≤ (5344769238343/12500000000000 : ℝ)^6349
        have hw : |(526032021/1000000000 : ℝ)|=(526032021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398684973/10000000000 : ℝ)|^8397 ≤ (22125953562131/50000000000000 : ℝ)^6349
        have hw : |(5398684973/10000000000 : ℝ)|=(5398684973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310898697/10000000000 : ℝ)*x 0 + (-1034432621/5000000000 : ℝ)*x 1 + (5398684347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310898697/10000000000 : ℝ)^8397 ≤ (43302735478199/100000000000000 : ℝ)^6349 := by
    have hnat : (5310898697 : ℕ)^8397*100000000000000^6349 ≤ 43302735478199^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310898697 10000000000 43302735478199 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034432621/5000000000 : ℝ)^8397 ≤ (12445364170233/100000000000000 : ℝ)^6349 := by
    have hnat : (1034432621 : ℕ)^8397*100000000000000^6349 ≤ 12445364170233^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034432621 5000000000 12445364170233 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398684347/10000000000 : ℝ)^8397 ≤ (22125950168949/50000000000000 : ℝ)^6349 := by
    have hnat : (5398684347 : ℕ)^8397*50000000000000^6349 ≤ 22125950168949^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398684347 10000000000 22125950168949 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310898697/10000000000 : ℝ), (-1034432621/5000000000 : ℝ), (5398684347/10000000000 : ℝ)] ![(43302735478199/100000000000000 : ℝ), (12445364170233/100000000000000 : ℝ), (22125950168949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310898697/10000000000 : ℝ)|^8397 ≤ (43302735478199/100000000000000 : ℝ)^6349
        have hw : |(5310898697/10000000000 : ℝ)|=(5310898697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034432621/5000000000 : ℝ)|^8397 ≤ (12445364170233/100000000000000 : ℝ)^6349
        have hw : |(-1034432621/5000000000 : ℝ)|=(1034432621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398684347/10000000000 : ℝ)|^8397 ≤ (22125950168949/50000000000000 : ℝ)^6349
        have hw : |(5398684347/10000000000 : ℝ)|=(5398684347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655449791/5000000000 : ℝ)*x 0 + (2699341861/5000000000 : ℝ)*x 1 + (-413772979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655449791/5000000000 : ℝ)^8397 ≤ (43302745021737/100000000000000 : ℝ)^6349 := by
    have hnat : (2655449791 : ℕ)^8397*100000000000000^6349 ≤ 43302745021737^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655449791 5000000000 43302745021737 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699341861/5000000000 : ℝ)^8397 ≤ (354015148499/800000000000 : ℝ)^6349 := by
    have hnat : (2699341861 : ℕ)^8397*800000000000^6349 ≤ 354015148499^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699341861 5000000000 354015148499 800000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413772979/2000000000 : ℝ)^8397 ≤ (388917544047/3125000000000 : ℝ)^6349 := by
    have hnat : (413772979 : ℕ)^8397*3125000000000^6349 ≤ 388917544047^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413772979 2000000000 388917544047 3125000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655449791/5000000000 : ℝ), (2699341861/5000000000 : ℝ), (-413772979/2000000000 : ℝ)] ![(43302745021737/100000000000000 : ℝ), (354015148499/800000000000 : ℝ), (388917544047/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655449791/5000000000 : ℝ)|^8397 ≤ (43302745021737/100000000000000 : ℝ)^6349
        have hw : |(2655449791/5000000000 : ℝ)|=(2655449791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699341861/5000000000 : ℝ)|^8397 ≤ (354015148499/800000000000 : ℝ)^6349
        have hw : |(2699341861/5000000000 : ℝ)|=(2699341861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413772979/2000000000 : ℝ)|^8397 ≤ (388917544047/3125000000000 : ℝ)^6349
        have hw : |(-413772979/2000000000 : ℝ)|=(413772979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s4_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355652681/10000000000 : ℝ)*x 0 + (4497161321/10000000000 : ℝ)*x 1 + (843707711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355652681/10000000000 : ℝ)^8397 ≤ (16656834702007/50000000000000 : ℝ)^6349 := by
    have hnat : (4355652681 : ℕ)^8397*50000000000000^6349 ≤ 16656834702007^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355652681 10000000000 16656834702007 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497161321/10000000000 : ℝ)^8397 ≤ (695050973269/2000000000000 : ℝ)^6349 := by
    have hnat : (4497161321 : ℕ)^8397*2000000000000^6349 ≤ 695050973269^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497161321 10000000000 695050973269 2000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843707711/2000000000 : ℝ)^8397 ≤ (3991722739551/12500000000000 : ℝ)^6349 := by
    have hnat : (843707711 : ℕ)^8397*12500000000000^6349 ≤ 3991722739551^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843707711 2000000000 3991722739551 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355652681/10000000000 : ℝ), (4497161321/10000000000 : ℝ), (843707711/2000000000 : ℝ)] ![(16656834702007/50000000000000 : ℝ), (695050973269/2000000000000 : ℝ), (3991722739551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355652681/10000000000 : ℝ)|^8397 ≤ (16656834702007/50000000000000 : ℝ)^6349
        have hw : |(4355652681/10000000000 : ℝ)|=(4355652681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497161321/10000000000 : ℝ)|^8397 ≤ (695050973269/2000000000000 : ℝ)^6349
        have hw : |(4497161321/10000000000 : ℝ)|=(4497161321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(843707711/2000000000 : ℝ)|^8397 ≤ (3991722739551/12500000000000 : ℝ)^6349
        have hw : |(843707711/2000000000 : ℝ)|=(843707711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10811/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (10945294521399891/100000000000000000000 : ℝ) := by
    have hpowers : (10811/100000 : ℝ)^2099 ≤ (10945294521399891/100000000000000000000 : ℝ)^512 := by
      have hnat : (10811 : ℕ)^2099*100000000000000000000^512 ≤ 10945294521399891^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10811 100000 10945294521399891 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10811/100000 : ℝ)) (X := (10945294521399891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (38976432218383977/100000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^2099 ≤ (38976432218383977/100000000000000000000 : ℝ)^512 := by
      have hnat : (14737 : ℕ)^2099*100000000000000000000^512 ≤ 38976432218383977^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 38976432218383977 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (38976432218383977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010945294521399891/50000000000000000000 : ℝ) ≤ (156258342554637/156250000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50010945294521399891/50000000000000000000 : ℝ)^512 ≤ (156258342554637/156250000000000 : ℝ)^2099 := by
      have hnat : (50010945294521399891 : ℕ)^512*156250000000000^2099 ≤ 156258342554637^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010945294521399891 50000000000000000000 156258342554637 156250000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156258342554637/156250000000000 : ℝ)) (X := (50010945294521399891/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012480431684945967/25000000000000000000 : ℝ) ≤ (10001217489364581/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25012480431684945967/25000000000000000000 : ℝ)^512 ≤ (10001217489364581/10000000000000000 : ℝ)^2099 := by
      have hnat : (25012480431684945967 : ℕ)^512*10000000000000000^2099 ≤ 10001217489364581^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012480431684945967 25000000000000000000 10001217489364581 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001217489364581/10000000000000000 : ℝ)) (X := (25012480431684945967/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038976432218383977/50000000000000000000 : ℝ) ≤ (5000950527616197/5000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50038976432218383977/50000000000000000000 : ℝ)^512 ≤ (5000950527616197/5000000000000000 : ℝ)^2099 := by
      have hnat : (50038976432218383977 : ℕ)^512*5000000000000000^2099 ≤ 5000950527616197^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038976432218383977 50000000000000000000 5000950527616197 5000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000950527616197/5000000000000000 : ℝ)) (X := (50038976432218383977/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10945294521399891/100000000000000000000 : ℝ) ≤ ((19623658061227229241/19630000000000000000 : ℝ)+2*(683565867813/392600000000000 : ℝ)*(10811/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (19623658061227229241/19630000000000000000 : ℝ)+2*(683565867813/392600000000000 : ℝ)*(10811/100000 : ℝ)=(156258342554637/156250000000000 : ℝ) by norm_num, show 1+2*(10945294521399891/100000000000000000000 : ℝ)=(50010945294521399891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38976432218383977/100000000000000000000 : ℝ)+(10945294521399891/100000000000000000000 : ℝ) ≤ ((19623658061227229241/19630000000000000000 : ℝ)+(683565867813/392600000000000 : ℝ)*((14737/100000 : ℝ)+(10811/100000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (19623658061227229241/19630000000000000000 : ℝ)+(683565867813/392600000000000 : ℝ)*((14737/100000 : ℝ)+(10811/100000 : ℝ))=(10001217489364581/10000000000000000 : ℝ) by norm_num, show 1+(38976432218383977/100000000000000000000 : ℝ)+(10945294521399891/100000000000000000000 : ℝ)=(25012480431684945967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38976432218383977/100000000000000000000 : ℝ) ≤ ((19623658061227229241/19630000000000000000 : ℝ)+2*(683565867813/392600000000000 : ℝ)*(14737/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (19623658061227229241/19630000000000000000 : ℝ)+2*(683565867813/392600000000000 : ℝ)*(14737/100000 : ℝ)=(5000950527616197/5000000000000000 : ℝ) by norm_num, show 1+2*(38976432218383977/100000000000000000000 : ℝ)=(50038976432218383977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19623658061227229241/19630000000000000000 : ℝ)*(X 1 0+X 2 0)+(683565867813/392600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (19623658061227229241/19630000000000000000 : ℝ)) (alpha := (683565867813/392600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19623658061227229241/19630000000000000000 : ℝ)*(X 0 1+X 2 1)+(683565867813/392600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (19623658061227229241/19630000000000000000 : ℝ)) (alpha := (683565867813/392600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19623658061227229241/19630000000000000000 : ℝ)*(X 0 2+X 1 2)+(683565867813/392600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (10811/100000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (19623658061227229241/19630000000000000000 : ℝ)) (alpha := (683565867813/392600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068474561/5000000000 : ℝ)*X 0 0+(5399074947/10000000000 : ℝ)*X 0 1+(5259931239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336576903/2500000000 : ℝ)*X 1 0+(-137976117/625000000 : ℝ)*X 1 1+(525993131/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336576899/2500000000 : ℝ)*X 2 0+(2629965627/5000000000 : ℝ)*X 2 1+(-2207617967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355639211/10000000000 : ℝ)*X 0 0+(4217751951/10000000000 : ℝ)*X 0 1+(89958903/200000000 : ℝ)*X 0 2+(4355639211/10000000000 : ℝ)*X 1 0+(4217751951/10000000000 : ℝ)*X 1 1+(89958903/200000000 : ℝ)*X 1 2+(4355639211/10000000000 : ℝ)*X 2 0+(4217751951/10000000000 : ℝ)*X 2 1+(89958903/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106847743/500000000 : ℝ)*X 0 0+(526032021/1000000000 : ℝ)*X 0 1+(5398684973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310898697/10000000000 : ℝ)*X 1 0+(-1034432621/5000000000 : ℝ)*X 1 1+(5398684347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655449791/5000000000 : ℝ)*X 2 0+(2699341861/5000000000 : ℝ)*X 2 1+(-413772979/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355652681/10000000000 : ℝ)*X 0 0+(4497161321/10000000000 : ℝ)*X 0 1+(843707711/2000000000 : ℝ)*X 0 2+(4355652681/10000000000 : ℝ)*X 1 0+(4497161321/10000000000 : ℝ)*X 1 1+(843707711/2000000000 : ℝ)*X 1 2+(4355652681/10000000000 : ℝ)*X 2 0+(4497161321/10000000000 : ℝ)*X 2 1+(843707711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17021239259467912052289/3926000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1250072521/100000000000000 : ℝ)*(base19) + (1088582459/100000000000000 : ℝ)*(base23) + (247510353/100000000000000 : ℝ)*(upper3) + (74838547/100000000000000 : ℝ)*(upper4) + (1575827/100000000000000 : ℝ)*(upper5) + (215117588780063/4000000000000 : ℝ)*(major0) + (215117588780063/4000000000000 : ℝ)*(major1) + (215117588780063/4000000000000 : ℝ)*(major2) + (898356504285689/12500000000000 : ℝ)*(sp0) + (1796719832067707/25000000000000 : ℝ)*(sp1) + (7186879489760889/100000000000000 : ℝ)*(sp2) + (446122471209893/12500000000000 : ℝ)*(sp3) + (7136014459/25000000000000 : ℝ)*(sp4) + (18946463417/100000000000000 : ℝ)*(sp7) + (1784499358071281/50000000000000 : ℝ)*(f.failure) + (7186880578343349/100000000000000 : ℝ)*(f.sum) + (11543073250433/3926000000000000000000000000 : ℝ)*base65 + (43674129464627817/78520000000000000000000000000000 : ℝ)*base68 + (979394190327747817/78520000000000000000000000000000 : ℝ)*base70 + (267108668745932183/78520000000000000000000000000000 : ℝ)*base71 + (425516802163/785200000000000000000000000 : ℝ)*base74 + (1378811052059427817/78520000000000000000000000000000 : ℝ)*base76 + (223885755865772183/78520000000000000000000000000000 : ℝ)*base77 + (738856867220732183/78520000000000000000000000000000 : ℝ)*base79 + (14130683525377/3926000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2234681/156250000000000000000 : ℝ)*base89 + (2234681/156250000000000000000 : ℝ)*base91 + (2234681/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9673993821805548537408457911/981500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142127247/50000000000000 : ℝ)*(base19) + (510521241/20000000000000 : ℝ)*(base23) + (24084577/20000000000000 : ℝ)*(lower2) + (6636623/1250000000000 : ℝ)*(lower4) + (13202159/20000000000000 : ℝ)*(upper5) + (5408205043990043/100000000000000 : ℝ)*(major0) + (5408205043990043/100000000000000 : ℝ)*(major1) + (5408205043990043/100000000000000 : ℝ)*(major2) + (23180358787/100000000000000 : ℝ)*(sp0) + (10913740199/25000000000000 : ℝ)*(sp2) + (1806825669945717/25000000000000 : ℝ)*(sp4) + (180683139397179/2500000000000 : ℝ)*(sp5) + (3613639826287327/50000000000000 : ℝ)*(sp6) + (3589083899293887/100000000000000 : ℝ)*(sp7) + (3589083899293887/100000000000000 : ℝ)*(f.failure) + (3613662930070827/50000000000000 : ℝ)*(f.sum) + (422852024479431/19630000000000000000000000000 : ℝ)*base66 + (46496865772332397363/1963000000000000000000000000000000 : ℝ)*base67 + (10910846713765602637/1963000000000000000000000000000000 : ℝ)*base70 + (10250708215359397363/1963000000000000000000000000000000 : ℝ)*base71 + (22482705288549/19630000000000000000000000000 : ℝ)*base73 + (3032139829834602637/1963000000000000000000000000000000 : ℝ)*base76 + (11769342876747397363/1963000000000000000000000000000000 : ℝ)*base77 + (17739840732043397363/1963000000000000000000000000000000 : ℝ)*base79 + (13891278208469/19630000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (586813/312500000000000000000 : ℝ)*base90 + (586813/312500000000000000000 : ℝ)*base92 + (586813/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s5_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137459993/10000000000 : ℝ)*x 0 + (5393336837/10000000000 : ℝ)*x 1 + (1316333481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137459993/10000000000 : ℝ)^8397 ≤ (2598800026751/20000000000000 : ℝ)^6349 := by
    have hnat : (2137459993 : ℕ)^8397*20000000000000^6349 ≤ 2598800026751^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137459993 10000000000 2598800026751 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393336837/10000000000 : ℝ)^8397 ≤ (8838787623363/20000000000000 : ℝ)^6349 := by
    have hnat : (5393336837 : ℕ)^8397*20000000000000^6349 ≤ 8838787623363^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393336837 10000000000 8838787623363 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316333481/2500000000 : ℝ)^8397 ≤ (5351507717701/12500000000000 : ℝ)^6349 := by
    have hnat : (1316333481 : ℕ)^8397*12500000000000^6349 ≤ 5351507717701^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316333481 2500000000 5351507717701 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137459993/10000000000 : ℝ), (5393336837/10000000000 : ℝ), (1316333481/2500000000 : ℝ)] ![(2598800026751/20000000000000 : ℝ), (8838787623363/20000000000000 : ℝ), (5351507717701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137459993/10000000000 : ℝ)|^8397 ≤ (2598800026751/20000000000000 : ℝ)^6349
        have hw : |(-2137459993/10000000000 : ℝ)|=(2137459993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393336837/10000000000 : ℝ)|^8397 ≤ (8838787623363/20000000000000 : ℝ)^6349
        have hw : |(5393336837/10000000000 : ℝ)|=(5393336837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316333481/2500000000 : ℝ)|^8397 ≤ (5351507717701/12500000000000 : ℝ)^6349
        have hw : |(1316333481/2500000000 : ℝ)|=(1316333481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672430537/5000000000 : ℝ)*x 0 + (-1101194993/5000000000 : ℝ)*x 1 + (5265333927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672430537/5000000000 : ℝ)^8397 ≤ (21834675679189/50000000000000 : ℝ)^6349 := by
    have hnat : (2672430537 : ℕ)^8397*50000000000000^6349 ≤ 21834675679189^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672430537 5000000000 21834675679189 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101194993/5000000000 : ℝ)^8397 ≤ (13518586856441/100000000000000 : ℝ)^6349 := by
    have hnat : (1101194993 : ℕ)^8397*100000000000000^6349 ≤ 13518586856441^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101194993 5000000000 13518586856441 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265333927/10000000000 : ℝ)^8397 ≤ (42812061773869/100000000000000 : ℝ)^6349 := by
    have hnat : (5265333927 : ℕ)^8397*100000000000000^6349 ≤ 42812061773869^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265333927 10000000000 42812061773869 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672430537/5000000000 : ℝ), (-1101194993/5000000000 : ℝ), (5265333927/10000000000 : ℝ)] ![(21834675679189/50000000000000 : ℝ), (13518586856441/100000000000000 : ℝ), (42812061773869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672430537/5000000000 : ℝ)|^8397 ≤ (21834675679189/50000000000000 : ℝ)^6349
        have hw : |(2672430537/5000000000 : ℝ)|=(2672430537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101194993/5000000000 : ℝ)|^8397 ≤ (13518586856441/100000000000000 : ℝ)^6349
        have hw : |(-1101194993/5000000000 : ℝ)|=(1101194993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265333927/10000000000 : ℝ)|^8397 ≤ (42812061773869/100000000000000 : ℝ)^6349
        have hw : |(5265333927/10000000000 : ℝ)|=(5265333927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106897221/200000000 : ℝ)*x 0 + (5265334003/10000000000 : ℝ)*x 1 + (-2202389917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106897221/200000000 : ℝ)^8397 ≤ (43669351099037/100000000000000 : ℝ)^6349 := by
    have hnat : (106897221 : ℕ)^8397*100000000000000^6349 ≤ 43669351099037^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106897221 200000000 43669351099037 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265334003/10000000000 : ℝ)^8397 ≤ (2675753911947/6250000000000 : ℝ)^6349 := by
    have hnat : (5265334003 : ℕ)^8397*6250000000000^6349 ≤ 2675753911947^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265334003 10000000000 2675753911947 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202389917/10000000000 : ℝ)^8397 ≤ (1351858629629/10000000000000 : ℝ)^6349 := by
    have hnat : (2202389917 : ℕ)^8397*10000000000000^6349 ≤ 1351858629629^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202389917 10000000000 1351858629629 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106897221/200000000 : ℝ), (5265334003/10000000000 : ℝ), (-2202389917/10000000000 : ℝ)] ![(43669351099037/100000000000000 : ℝ), (2675753911947/6250000000000 : ℝ), (1351858629629/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106897221/200000000 : ℝ)|^8397 ≤ (43669351099037/100000000000000 : ℝ)^6349
        have hw : |(106897221/200000000 : ℝ)|=(106897221/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265334003/10000000000 : ℝ)|^8397 ≤ (2675753911947/6250000000000 : ℝ)^6349
        have hw : |(5265334003/10000000000 : ℝ)|=(5265334003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202389917/10000000000 : ℝ)|^8397 ≤ (1351858629629/10000000000000 : ℝ)^6349
        have hw : |(-2202389917/10000000000 : ℝ)|=(2202389917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435593987/1000000000 : ℝ)*x 0 + (1057232659/2500000000 : ℝ)*x 1 + (4486689219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435593987/1000000000 : ℝ)^8397 ≤ (4164571812491/12500000000000 : ℝ)^6349 := by
    have hnat : (435593987 : ℕ)^8397*12500000000000^6349 ≤ 4164571812491^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435593987 1000000000 4164571812491 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057232659/2500000000 : ℝ)^8397 ≤ (3203786546807/10000000000000 : ℝ)^6349 := by
    have hnat : (1057232659 : ℕ)^8397*10000000000000^6349 ≤ 3203786546807^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057232659 2500000000 3203786546807 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486689219/10000000000 : ℝ)^8397 ≤ (34645560025411/100000000000000 : ℝ)^6349 := by
    have hnat : (4486689219 : ℕ)^8397*100000000000000^6349 ≤ 34645560025411^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486689219 10000000000 34645560025411 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435593987/1000000000 : ℝ), (1057232659/2500000000 : ℝ), (4486689219/10000000000 : ℝ)] ![(4164571812491/12500000000000 : ℝ), (3203786546807/10000000000000 : ℝ), (34645560025411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435593987/1000000000 : ℝ)|^8397 ≤ (4164571812491/12500000000000 : ℝ)^6349
        have hw : |(435593987/1000000000 : ℝ)|=(435593987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057232659/2500000000 : ℝ)|^8397 ≤ (3203786546807/10000000000000 : ℝ)^6349
        have hw : |(1057232659/2500000000 : ℝ)|=(1057232659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486689219/10000000000 : ℝ)|^8397 ≤ (34645560025411/100000000000000 : ℝ)^6349
        have hw : |(4486689219/10000000000 : ℝ)|=(4486689219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137464721/10000000000 : ℝ)*x 0 + (82276001/156250000 : ℝ)*x 1 + (539300573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137464721/10000000000 : ℝ)^8397 ≤ (6497019073779/50000000000000 : ℝ)^6349 := by
    have hnat : (2137464721 : ℕ)^8397*50000000000000^6349 ≤ 6497019073779^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137464721 10000000000 6497019073779 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82276001/156250000 : ℝ)^8397 ≤ (21407806006647/50000000000000 : ℝ)^6349 := by
    have hnat : (82276001 : ℕ)^8397*50000000000000^6349 ≤ 21407806006647^6349*156250000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82276001 156250000 21407806006647 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539300573/1000000000 : ℝ)^8397 ≤ (22095174911293/50000000000000 : ℝ)^6349 := by
    have hnat : (539300573 : ℕ)^8397*50000000000000^6349 ≤ 22095174911293^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539300573 1000000000 22095174911293 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137464721/10000000000 : ℝ), (82276001/156250000 : ℝ), (539300573/1000000000 : ℝ)] ![(6497019073779/50000000000000 : ℝ), (21407806006647/50000000000000 : ℝ), (22095174911293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137464721/10000000000 : ℝ)|^8397 ≤ (6497019073779/50000000000000 : ℝ)^6349
        have hw : |(-2137464721/10000000000 : ℝ)|=(2137464721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82276001/156250000 : ℝ)|^8397 ≤ (21407806006647/50000000000000 : ℝ)^6349
        have hw : |(82276001/156250000 : ℝ)|=(82276001/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539300573/1000000000 : ℝ)|^8397 ≤ (22095174911293/50000000000000 : ℝ)^6349
        have hw : |(539300573/1000000000 : ℝ)|=(539300573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312286783/10000000000 : ℝ)*x 0 + (-518679383/2500000000 : ℝ)*x 1 + (269650283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312286783/10000000000 : ℝ)^8397 ≤ (43317704755051/100000000000000 : ℝ)^6349 := by
    have hnat : (5312286783 : ℕ)^8397*100000000000000^6349 ≤ 43317704755051^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312286783 10000000000 43317704755051 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518679383/2500000000 : ℝ)^8397 ≤ (6245973080201/50000000000000 : ℝ)^6349 := by
    have hnat : (518679383 : ℕ)^8397*50000000000000^6349 ≤ 6245973080201^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518679383 2500000000 6245973080201 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269650283/500000000 : ℝ)^8397 ≤ (8838069812797/20000000000000 : ℝ)^6349 := by
    have hnat : (269650283 : ℕ)^8397*20000000000000^6349 ≤ 8838069812797^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269650283 500000000 8838069812797 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312286783/10000000000 : ℝ), (-518679383/2500000000 : ℝ), (269650283/500000000 : ℝ)] ![(43317704755051/100000000000000 : ℝ), (6245973080201/50000000000000 : ℝ), (8838069812797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312286783/10000000000 : ℝ)|^8397 ≤ (43317704755051/100000000000000 : ℝ)^6349
        have hw : |(5312286783/10000000000 : ℝ)|=(5312286783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518679383/2500000000 : ℝ)|^8397 ≤ (6245973080201/50000000000000 : ℝ)^6349
        have hw : |(-518679383/2500000000 : ℝ)|=(518679383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269650283/500000000 : ℝ)|^8397 ≤ (8838069812797/20000000000000 : ℝ)^6349
        have hw : |(269650283/500000000 : ℝ)|=(269650283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656143107/5000000000 : ℝ)*x 0 + (5393006323/10000000000 : ℝ)*x 1 + (-2074717401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656143107/5000000000 : ℝ)^8397 ≤ (5414712327329/12500000000000 : ℝ)^6349 := by
    have hnat : (2656143107 : ℕ)^8397*12500000000000^6349 ≤ 5414712327329^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656143107 5000000000 5414712327329 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393006323/10000000000 : ℝ)^8397 ≤ (2209517812451/5000000000000 : ℝ)^6349 := by
    have hnat : (5393006323 : ℕ)^8397*5000000000000^6349 ≤ 2209517812451^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393006323 10000000000 2209517812451 5000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074717401/10000000000 : ℝ)^8397 ≤ (6245972558609/50000000000000 : ℝ)^6349 := by
    have hnat : (2074717401 : ℕ)^8397*50000000000000^6349 ≤ 6245972558609^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074717401 10000000000 6245972558609 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656143107/5000000000 : ℝ), (5393006323/10000000000 : ℝ), (-2074717401/10000000000 : ℝ)] ![(5414712327329/12500000000000 : ℝ), (2209517812451/5000000000000 : ℝ), (6245972558609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656143107/5000000000 : ℝ)|^8397 ≤ (5414712327329/12500000000000 : ℝ)^6349
        have hw : |(2656143107/5000000000 : ℝ)|=(2656143107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393006323/10000000000 : ℝ)|^8397 ≤ (2209517812451/5000000000000 : ℝ)^6349
        have hw : |(5393006323/10000000000 : ℝ)|=(5393006323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074717401/10000000000 : ℝ)|^8397 ≤ (6245972558609/50000000000000 : ℝ)^6349
        have hw : |(-2074717401/10000000000 : ℝ)|=(2074717401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177975299/5000000000 : ℝ)*x 0 + (897205103/2000000000 : ℝ)*x 1 + (528699533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177975299/5000000000 : ℝ)^8397 ≤ (16658341510769/50000000000000 : ℝ)^6349 := by
    have hnat : (2177975299 : ℕ)^8397*50000000000000^6349 ≤ 16658341510769^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177975299 5000000000 16658341510769 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897205103/2000000000 : ℝ)^8397 ≤ (34638781979647/100000000000000 : ℝ)^6349 := by
    have hnat : (897205103 : ℕ)^8397*100000000000000^6349 ≤ 34638781979647^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897205103 2000000000 34638781979647 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528699533/1250000000 : ℝ)^8397 ≤ (8011133746501/25000000000000 : ℝ)^6349 := by
    have hnat : (528699533 : ℕ)^8397*25000000000000^6349 ≤ 8011133746501^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528699533 1250000000 8011133746501 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177975299/5000000000 : ℝ), (897205103/2000000000 : ℝ), (528699533/1250000000 : ℝ)] ![(16658341510769/50000000000000 : ℝ), (34638781979647/100000000000000 : ℝ), (8011133746501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177975299/5000000000 : ℝ)|^8397 ≤ (16658341510769/50000000000000 : ℝ)^6349
        have hw : |(2177975299/5000000000 : ℝ)|=(2177975299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897205103/2000000000 : ℝ)|^8397 ≤ (34638781979647/100000000000000 : ℝ)^6349
        have hw : |(897205103/2000000000 : ℝ)|=(897205103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528699533/1250000000 : ℝ)|^8397 ≤ (8011133746501/25000000000000 : ℝ)^6349
        have hw : |(528699533/1250000000 : ℝ)|=(528699533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s5_8 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220029/25000000 : ℝ)*x 0 + (2836919893/5000000000 : ℝ)*x 1 + (122956759/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220029/25000000 : ℝ)^8397 ≤ (191209366747/100000000000000 : ℝ)^6349 := by
    have hnat : (220029 : ℕ)^8397*100000000000000^6349 ≤ 191209366747^6349*25000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220029 25000000 191209366747 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2836919893/5000000000 : ℝ)^8397 ≤ (47259059579463/100000000000000 : ℝ)^6349 := by
    have hnat : (2836919893 : ℕ)^8397*100000000000000^6349 ≤ 47259059579463^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836919893 5000000000 47259059579463 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122956759/200000000 : ℝ)^8397 ≤ (26274865520837/50000000000000 : ℝ)^6349 := by
    have hnat : (122956759 : ℕ)^8397*50000000000000^6349 ≤ 26274865520837^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122956759 200000000 26274865520837 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220029/25000000 : ℝ), (2836919893/5000000000 : ℝ), (122956759/200000000 : ℝ)] ![(191209366747/100000000000000 : ℝ), (47259059579463/100000000000000 : ℝ), (26274865520837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220029/25000000 : ℝ)|^8397 ≤ (191209366747/100000000000000 : ℝ)^6349
        have hw : |(-220029/25000000 : ℝ)|=(220029/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2836919893/5000000000 : ℝ)|^8397 ≤ (47259059579463/100000000000000 : ℝ)^6349
        have hw : |(2836919893/5000000000 : ℝ)|=(2836919893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122956759/200000000 : ℝ)|^8397 ≤ (26274865520837/50000000000000 : ℝ)^6349
        have hw : |(122956759/200000000 : ℝ)|=(122956759/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (2099/512 : ℝ) ≤ (6532355007455299/50000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^2099 ≤ (6532355007455299/50000000000000000000 : ℝ)^512 := by
      have hnat : (1411 : ℕ)^2099*50000000000000000000^512 ≤ 6532355007455299^512*12500^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 6532355007455299 50000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (6532355007455299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2099/512 : ℝ) ≤ (8453496194533347/25000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2099 ≤ (8453496194533347/25000000000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2099*25000000000000000000^512 ≤ 8453496194533347^512*20000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 8453496194533347 25000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (8453496194533347/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006532355007455299/25000000000000000000 : ℝ) ≤ (10000637300703527/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25006532355007455299/25000000000000000000 : ℝ)^512 ≤ (10000637300703527/10000000000000000 : ℝ)^2099 := by
      have hnat : (25006532355007455299 : ℕ)^512*10000000000000000^2099 ≤ 10000637300703527^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006532355007455299 25000000000000000000 10000637300703527 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000637300703527/10000000000000000 : ℝ)) (X := (25006532355007455299/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023439347396521993/50000000000000000000 : ℝ) ≤ (5000571644576283/5000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50023439347396521993/50000000000000000000 : ℝ)^512 ≤ (5000571644576283/5000000000000000 : ℝ)^2099 := by
      have hnat : (50023439347396521993 : ℕ)^512*5000000000000000^2099 ≤ 5000571644576283^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023439347396521993 50000000000000000000 5000571644576283 5000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000571644576283/5000000000000000 : ℝ)) (X := (50023439347396521993/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508453496194533347/12500000000000000000 : ℝ) ≤ (2000329855520321/2000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (12508453496194533347/12500000000000000000 : ℝ)^512 ≤ (2000329855520321/2000000000000000 : ℝ)^2099 := by
      have hnat : (12508453496194533347 : ℕ)^512*2000000000000000^2099 ≤ 2000329855520321^2099*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508453496194533347 12500000000000000000 2000329855520321 2000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000329855520321/2000000000000000 : ℝ)) (X := (12508453496194533347/12500000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6532355007455299/50000000000000000000 : ℝ) ≤ ((5892090985989557921/5894000000000000000 : ℝ)+2*(505988449039/294700000000000 : ℝ)*(1411/12500 : ℝ))^(2099/512 : ℝ) := by
    rw [show (5892090985989557921/5894000000000000000 : ℝ)+2*(505988449039/294700000000000 : ℝ)*(1411/12500 : ℝ)=(10000637300703527/10000000000000000 : ℝ) by norm_num, show 1+2*(6532355007455299/50000000000000000000 : ℝ)=(25006532355007455299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8453496194533347/25000000000000000000 : ℝ)+(6532355007455299/50000000000000000000 : ℝ) ≤ ((5892090985989557921/5894000000000000000 : ℝ)+(505988449039/294700000000000 : ℝ)*((2847/20000 : ℝ)+(1411/12500 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (5892090985989557921/5894000000000000000 : ℝ)+(505988449039/294700000000000 : ℝ)*((2847/20000 : ℝ)+(1411/12500 : ℝ))=(5000571644576283/5000000000000000 : ℝ) by norm_num, show 1+(8453496194533347/25000000000000000000 : ℝ)+(6532355007455299/50000000000000000000 : ℝ)=(50023439347396521993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8453496194533347/25000000000000000000 : ℝ) ≤ ((5892090985989557921/5894000000000000000 : ℝ)+2*(505988449039/294700000000000 : ℝ)*(2847/20000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (5892090985989557921/5894000000000000000 : ℝ)+2*(505988449039/294700000000000 : ℝ)*(2847/20000 : ℝ)=(2000329855520321/2000000000000000 : ℝ) by norm_num, show 1+2*(8453496194533347/25000000000000000000 : ℝ)=(12508453496194533347/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5892090985989557921/5894000000000000000 : ℝ)*(X 1 0+X 2 0)+(505988449039/294700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5892090985989557921/5894000000000000000 : ℝ)) (alpha := (505988449039/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5892090985989557921/5894000000000000000 : ℝ)*(X 0 1+X 2 1)+(505988449039/294700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5892090985989557921/5894000000000000000 : ℝ)) (alpha := (505988449039/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5892090985989557921/5894000000000000000 : ℝ)*(X 0 2+X 1 2)+(505988449039/294700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5892090985989557921/5894000000000000000 : ℝ)) (alpha := (505988449039/294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2137459993/10000000000 : ℝ)*X 0 0+(5393336837/10000000000 : ℝ)*X 0 1+(1316333481/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672430537/5000000000 : ℝ)*X 1 0+(-1101194993/5000000000 : ℝ)*X 1 1+(5265333927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106897221/200000000 : ℝ)*X 2 0+(5265334003/10000000000 : ℝ)*X 2 1+(-2202389917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435593987/1000000000 : ℝ)*X 0 0+(1057232659/2500000000 : ℝ)*X 0 1+(4486689219/10000000000 : ℝ)*X 0 2+(435593987/1000000000 : ℝ)*X 1 0+(1057232659/2500000000 : ℝ)*X 1 1+(4486689219/10000000000 : ℝ)*X 1 2+(435593987/1000000000 : ℝ)*X 2 0+(1057232659/2500000000 : ℝ)*X 2 1+(4486689219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137464721/10000000000 : ℝ)*X 0 0+(82276001/156250000 : ℝ)*X 0 1+(539300573/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312286783/10000000000 : ℝ)*X 1 0+(-518679383/2500000000 : ℝ)*X 1 1+(269650283/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656143107/5000000000 : ℝ)*X 2 0+(5393006323/10000000000 : ℝ)*X 2 1+(-2074717401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177975299/5000000000 : ℝ)*X 0 0+(897205103/2000000000 : ℝ)*X 0 1+(528699533/1250000000 : ℝ)*X 0 2+(2177975299/5000000000 : ℝ)*X 1 0+(897205103/2000000000 : ℝ)*X 1 1+(528699533/1250000000 : ℝ)*X 1 2+(2177975299/5000000000 : ℝ)*X 2 0+(897205103/2000000000 : ℝ)*X 2 1+(528699533/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-220029/25000000 : ℝ)*X 0 0+(2836919893/5000000000 : ℝ)*X 0 1+(122956759/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1371907663710170445613670511/147350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477141589/100000000000000 : ℝ)*(lower2) + (241558291/100000000000000 : ℝ)*(lower3) + (61620711/12500000000000 : ℝ)*(lower4) + (141734493/100000000000000 : ℝ)*(lower5) + (5845970936078597/100000000000000 : ℝ)*(major0) + (5845970936078597/100000000000000 : ℝ)*(major1) + (5845970936078597/100000000000000 : ℝ)*(major2) + (7812335438007283/100000000000000 : ℝ)*(sp0) + (7812326943819649/100000000000000 : ℝ)*(sp1) + (7812327842129309/100000000000000 : ℝ)*(sp2) + (1939800727945397/50000000000000 : ℝ)*(sp3) + (102828871/781250000000 : ℝ)*(sp5) + (3065946457/25000000000000 : ℝ)*(sp6) + (291744241/6250000000000 : ℝ)*(sp8) + (1939800727945397/50000000000000 : ℝ)*(f.failure) + (3906170052957569/50000000000000 : ℝ)*(f.sum) + (161640805071013/3683750000000000000000000000 : ℝ)*base66 + (14471836113581823163/589400000000000000000000000000000 : ℝ)*base68 + (13386718831167623163/589400000000000000000000000000000 : ℝ)*base70 + (16982342528248423163/589400000000000000000000000000000 : ℝ)*base72 + (16219610561407/14735000000000000000000000000 : ℝ)*base74 + (4389227243651023163/589400000000000000000000000000000 : ℝ)*base76 + (16043088306578776837/589400000000000000000000000000000 : ℝ)*base77 + (9102073042131423163/589400000000000000000000000000000 : ℝ)*base80 + (7059173528027/3683750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (66197/156250000000000000000 : ℝ)*base89 + (66197/156250000000000000000 : ℝ)*base91 + (66197/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (239800550919615159387/117880000000000000000000000 : ℝ) := by norm_num
    linear_combination (470645073/100000000000000 : ℝ)*(lower2) + (383932061/100000000000000 : ℝ)*(lower3) + (427314451/50000000000000 : ℝ)*(lower4) + (14261747/5000000000000 : ℝ)*(lower5) + (1175258892523101/20000000000000 : ℝ)*(major0) + (1175258892523101/20000000000000 : ℝ)*(major1) + (1175258892523101/20000000000000 : ℝ)*(major2) + (19292228193/100000000000000 : ℝ)*(sp2) + (5882969749/50000000000000 : ℝ)*(sp3) + (785285923527707/10000000000000 : ℝ)*(sp4) + (3926431796679181/50000000000000 : ℝ)*(sp5) + (7852844301130169/100000000000000 : ℝ)*(sp6) + (487464187265489/12500000000000 : ℝ)*(sp7) + (1089520323/25000000000000 : ℝ)*(sp8) + (389972526406341/10000000000000 : ℝ)*(f.failure) + (3926431796679181/50000000000000 : ℝ)*(f.sum) + (2044960100137/2947000000000000000000000000 : ℝ)*base65 + (48137345636813021/117880000000000000000000000000000 : ℝ)*base67 + (1488476541151586979/117880000000000000000000000000000 : ℝ)*base70 + (8789641594282653021/117880000000000000000000000000000 : ℝ)*base71 + (13874211862389/2947000000000000000000000000 : ℝ)*base74 + (647027351658813021/117880000000000000000000000000000 : ℝ)*base75 + (32573446172946979/117880000000000000000000000000000 : ℝ)*base78 + (181387883794306979/117880000000000000000000000000000 : ℝ)*base80 + (2358406377821/2947000000000000000000000000 : ℝ)*base82 + (228741/31250000000000000000 : ℝ)*base89 + (228741/31250000000000000000 : ℝ)*base91 + (228741/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1204_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1204_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1204_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1204_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1204_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (653/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
