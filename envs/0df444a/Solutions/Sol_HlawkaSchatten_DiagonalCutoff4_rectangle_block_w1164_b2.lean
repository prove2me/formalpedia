-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:45.569363+00:00
-- url     : https://prove2.me/submissions/fe480d97-b46c-4974-bb18-2dd3726d35a1

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
theorem support_rectangle_w1164_s6_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078190989/5000000000 : ℝ)*x 0 + (26964713/50000000 : ℝ)*x 1 + (2632899343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078190989/5000000000 : ℝ)^8357 ≤ (2621033890457/20000000000000 : ℝ)^6309 := by
    have hnat : (1078190989 : ℕ)^8357*20000000000000^6309 ≤ 2621033890457^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078190989 5000000000 2621033890457 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26964713/50000000 : ℝ)^8357 ≤ (353071162673/800000000000 : ℝ)^6309 := by
    have hnat : (26964713 : ℕ)^8357*800000000000^6309 ≤ 353071162673^6309*50000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26964713 50000000 353071162673 800000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632899343/5000000000 : ℝ)^8357 ≤ (2138046760013/5000000000000 : ℝ)^6309 := by
    have hnat : (2632899343 : ℕ)^8357*5000000000000^6309 ≤ 2138046760013^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632899343 5000000000 2138046760013 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078190989/5000000000 : ℝ), (26964713/50000000 : ℝ), (2632899343/5000000000 : ℝ)] ![(2621033890457/20000000000000 : ℝ), (353071162673/800000000000 : ℝ), (2138046760013/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078190989/5000000000 : ℝ)|^8357 ≤ (2621033890457/20000000000000 : ℝ)^6309
        have hw : |(-1078190989/5000000000 : ℝ)|=(1078190989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26964713/50000000 : ℝ)|^8357 ≤ (353071162673/800000000000 : ℝ)^6309
        have hw : |(26964713/50000000 : ℝ)|=(26964713/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632899343/5000000000 : ℝ)|^8357 ≤ (2138046760013/5000000000000 : ℝ)^6309
        have hw : |(2632899343/5000000000 : ℝ)|=(2632899343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267237519/500000000 : ℝ)*x 0 + (-277608853/1250000000 : ℝ)*x 1 + (5265798819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267237519/500000000 : ℝ)^8357 ≤ (43612242423971/100000000000000 : ℝ)^6309 := by
    have hnat : (267237519 : ℕ)^8357*100000000000000^6309 ≤ 43612242423971^6309*500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267237519 500000000 43612242423971 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277608853/1250000000 : ℝ)^8357 ≤ (53229769229/390625000000 : ℝ)^6309 := by
    have hnat : (277608853 : ℕ)^8357*390625000000^6309 ≤ 53229769229^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277608853 1250000000 53229769229 390625000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265798819/10000000000 : ℝ)^8357 ≤ (42760936630881/100000000000000 : ℝ)^6309 := by
    have hnat : (5265798819 : ℕ)^8357*100000000000000^6309 ≤ 42760936630881^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265798819 10000000000 42760936630881 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267237519/500000000 : ℝ), (-277608853/1250000000 : ℝ), (5265798819/10000000000 : ℝ)] ![(43612242423971/100000000000000 : ℝ), (53229769229/390625000000 : ℝ), (42760936630881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267237519/500000000 : ℝ)|^8357 ≤ (43612242423971/100000000000000 : ℝ)^6309
        have hw : |(267237519/500000000 : ℝ)|=(267237519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277608853/1250000000 : ℝ)|^8357 ≤ (53229769229/390625000000 : ℝ)^6309
        have hw : |(-277608853/1250000000 : ℝ)|=(277608853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265798819/10000000000 : ℝ)|^8357 ≤ (42760936630881/100000000000000 : ℝ)^6309
        have hw : |(5265798819/10000000000 : ℝ)|=(5265798819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344750747/10000000000 : ℝ)*x 0 + (5265798253/10000000000 : ℝ)*x 1 + (-1110435543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344750747/10000000000 : ℝ)^8357 ≤ (2180612319537/5000000000000 : ℝ)^6309 := by
    have hnat : (5344750747 : ℕ)^8357*5000000000000^6309 ≤ 2180612319537^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344750747 10000000000 2180612319537 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265798253/10000000000 : ℝ)^8357 ≤ (10690232635669/25000000000000 : ℝ)^6309 := by
    have hnat : (5265798253 : ℕ)^8357*25000000000000^6309 ≤ 10690232635669^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265798253 10000000000 10690232635669 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110435543/5000000000 : ℝ)^8357 ≤ (13626823052049/100000000000000 : ℝ)^6309 := by
    have hnat : (1110435543 : ℕ)^8357*100000000000000^6309 ≤ 13626823052049^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110435543 5000000000 13626823052049 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344750747/10000000000 : ℝ), (5265798253/10000000000 : ℝ), (-1110435543/5000000000 : ℝ)] ![(2180612319537/5000000000000 : ℝ), (10690232635669/25000000000000 : ℝ), (13626823052049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344750747/10000000000 : ℝ)|^8357 ≤ (2180612319537/5000000000000 : ℝ)^6309
        have hw : |(5344750747/10000000000 : ℝ)|=(5344750747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265798253/10000000000 : ℝ)|^8357 ≤ (10690232635669/25000000000000 : ℝ)^6309
        have hw : |(5265798253/10000000000 : ℝ)|=(5265798253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110435543/5000000000 : ℝ)|^8357 ≤ (13626823052049/100000000000000 : ℝ)^6309
        have hw : |(-1110435543/5000000000 : ℝ)|=(1110435543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436156827/1000000000 : ℝ)*x 0 + (847275407/2000000000 : ℝ)*x 1 + (70162817/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436156827/1000000000 : ℝ)^8357 ≤ (16658468019907/50000000000000 : ℝ)^6309 := by
    have hnat : (436156827 : ℕ)^8357*50000000000000^6309 ≤ 16658468019907^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436156827 1000000000 16658468019907 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847275407/2000000000 : ℝ)^8357 ≤ (1602806993639/5000000000000 : ℝ)^6309 := by
    have hnat : (847275407 : ℕ)^8357*5000000000000^6309 ≤ 1602806993639^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847275407 2000000000 1602806993639 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70162817/156250000 : ℝ)^8357 ≤ (692538481303/2000000000000 : ℝ)^6309 := by
    have hnat : (70162817 : ℕ)^8357*2000000000000^6309 ≤ 692538481303^6309*156250000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70162817 156250000 692538481303 2000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436156827/1000000000 : ℝ), (847275407/2000000000 : ℝ), (70162817/156250000 : ℝ)] ![(16658468019907/50000000000000 : ℝ), (1602806993639/5000000000000 : ℝ), (692538481303/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436156827/1000000000 : ℝ)|^8357 ≤ (16658468019907/50000000000000 : ℝ)^6309
        have hw : |(436156827/1000000000 : ℝ)|=(436156827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847275407/2000000000 : ℝ)|^8357 ≤ (1602806993639/5000000000000 : ℝ)^6309
        have hw : |(847275407/2000000000 : ℝ)|=(847275407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70162817/156250000 : ℝ)|^8357 ≤ (692538481303/2000000000000 : ℝ)^6309
        have hw : |(70162817/156250000 : ℝ)|=(70162817/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156387257/10000000000 : ℝ)*x 0 + (526611943/1000000000 : ℝ)*x 1 + (1348155101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156387257/10000000000 : ℝ)^8357 ≤ (13105211949323/100000000000000 : ℝ)^6309 := by
    have hnat : (2156387257 : ℕ)^8357*100000000000000^6309 ≤ 13105211949323^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156387257 10000000000 13105211949323 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526611943/1000000000 : ℝ)^8357 ≤ (2672774083237/6250000000000 : ℝ)^6309 := by
    have hnat : (526611943 : ℕ)^8357*6250000000000^6309 ≤ 2672774083237^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526611943 1000000000 2672774083237 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348155101/2500000000 : ℝ)^8357 ≤ (22065201353307/50000000000000 : ℝ)^6309 := by
    have hnat : (1348155101 : ℕ)^8357*50000000000000^6309 ≤ 22065201353307^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348155101 2500000000 22065201353307 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156387257/10000000000 : ℝ), (526611943/1000000000 : ℝ), (1348155101/2500000000 : ℝ)] ![(13105211949323/100000000000000 : ℝ), (2672774083237/6250000000000 : ℝ), (22065201353307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156387257/10000000000 : ℝ)|^8357 ≤ (13105211949323/100000000000000 : ℝ)^6309
        have hw : |(-2156387257/10000000000 : ℝ)|=(2156387257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526611943/1000000000 : ℝ)|^8357 ≤ (2672774083237/6250000000000 : ℝ)^6309
        have hw : |(526611943/1000000000 : ℝ)|=(526611943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348155101/2500000000 : ℝ)|^8357 ≤ (22065201353307/50000000000000 : ℝ)^6309
        have hw : |(1348155101/2500000000 : ℝ)|=(1348155101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328121533/2500000000 : ℝ)*x 0 + (-523512233/2500000000 : ℝ)*x 1 + (539262037/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328121533/2500000000 : ℝ)^8357 ≤ (43263852082989/100000000000000 : ℝ)^6309 := by
    have hnat : (1328121533 : ℕ)^8357*100000000000000^6309 ≤ 43263852082989^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328121533 2500000000 43263852082989 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523512233/2500000000 : ℝ)^8357 ≤ (984823873/7812500000 : ℝ)^6309 := by
    have hnat : (523512233 : ℕ)^8357*7812500000^6309 ≤ 984823873^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523512233 2500000000 984823873 7812500000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539262037/1000000000 : ℝ)^8357 ≤ (8826080467611/20000000000000 : ℝ)^6309 := by
    have hnat : (539262037 : ℕ)^8357*20000000000000^6309 ≤ 8826080467611^6309*1000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539262037 1000000000 8826080467611 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328121533/2500000000 : ℝ), (-523512233/2500000000 : ℝ), (539262037/1000000000 : ℝ)] ![(43263852082989/100000000000000 : ℝ), (984823873/7812500000 : ℝ), (8826080467611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328121533/2500000000 : ℝ)|^8357 ≤ (43263852082989/100000000000000 : ℝ)^6309
        have hw : |(1328121533/2500000000 : ℝ)|=(1328121533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523512233/2500000000 : ℝ)|^8357 ≤ (984823873/7812500000 : ℝ)^6309
        have hw : |(-523512233/2500000000 : ℝ)|=(523512233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539262037/1000000000 : ℝ)|^8357 ≤ (8826080467611/20000000000000 : ℝ)^6309
        have hw : |(539262037/1000000000 : ℝ)|=(539262037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20751899/39062500 : ℝ)*x 0 + (215704813/400000000 : ℝ)*x 1 + (-130878061/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20751899/39062500 : ℝ)^8357 ≤ (21631926106219/50000000000000 : ℝ)^6309 := by
    have hnat : (20751899 : ℕ)^8357*50000000000000^6309 ≤ 21631926106219^6309*39062500^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20751899 39062500 21631926106219 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215704813/400000000 : ℝ)^8357 ≤ (2758150115641/6250000000000 : ℝ)^6309 := by
    have hnat : (215704813 : ℕ)^8357*6250000000000^6309 ≤ 2758150115641^6309*400000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215704813 400000000 2758150115641 6250000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130878061/625000000 : ℝ)^8357 ≤ (12605745925253/100000000000000 : ℝ)^6309 := by
    have hnat : (130878061 : ℕ)^8357*100000000000000^6309 ≤ 12605745925253^6309*625000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130878061 625000000 12605745925253 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20751899/39062500 : ℝ), (215704813/400000000 : ℝ), (-130878061/625000000 : ℝ)] ![(21631926106219/50000000000000 : ℝ), (2758150115641/6250000000000 : ℝ), (12605745925253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20751899/39062500 : ℝ)|^8357 ≤ (21631926106219/50000000000000 : ℝ)^6309
        have hw : |(20751899/39062500 : ℝ)|=(20751899/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215704813/400000000 : ℝ)|^8357 ≤ (2758150115641/6250000000000 : ℝ)^6309
        have hw : |(215704813/400000000 : ℝ)|=(215704813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130878061/625000000 : ℝ)|^8357 ≤ (12605745925253/100000000000000 : ℝ)^6309
        have hw : |(-130878061/625000000 : ℝ)|=(130878061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s6_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180788751/5000000000 : ℝ)*x 0 + (4489778449/10000000000 : ℝ)*x 1 + (2118510887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180788751/5000000000 : ℝ)^8357 ≤ (8329257363251/25000000000000 : ℝ)^6309 := by
    have hnat : (2180788751 : ℕ)^8357*25000000000000^6309 ≤ 8329257363251^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180788751 5000000000 8329257363251 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489778449/10000000000 : ℝ)^8357 ≤ (34620368157539/100000000000000 : ℝ)^6309 := by
    have hnat : (4489778449 : ℕ)^8357*100000000000000^6309 ≤ 34620368157539^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489778449 10000000000 34620368157539 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118510887/5000000000 : ℝ)^8357 ≤ (32062602381807/100000000000000 : ℝ)^6309 := by
    have hnat : (2118510887 : ℕ)^8357*100000000000000^6309 ≤ 32062602381807^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118510887 5000000000 32062602381807 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180788751/5000000000 : ℝ), (4489778449/10000000000 : ℝ), (2118510887/5000000000 : ℝ)] ![(8329257363251/25000000000000 : ℝ), (34620368157539/100000000000000 : ℝ), (32062602381807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180788751/5000000000 : ℝ)|^8357 ≤ (8329257363251/25000000000000 : ℝ)^6309
        have hw : |(2180788751/5000000000 : ℝ)|=(2180788751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489778449/10000000000 : ℝ)|^8357 ≤ (34620368157539/100000000000000 : ℝ)^6309
        have hw : |(4489778449/10000000000 : ℝ)|=(4489778449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118510887/5000000000 : ℝ)|^8357 ≤ (32062602381807/100000000000000 : ℝ)^6309
        have hw : |(2118510887/5000000000 : ℝ)|=(2118510887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (2089/512 : ℝ) ≤ (139264641788839/1000000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^2089 ≤ (139264641788839/1000000000000000000 : ℝ)^512 := by
      have hnat : (11347 : ℕ)^2089*1000000000000000000^512 ≤ 139264641788839^512*100000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 139264641788839 1000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (139264641788839/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (2089/512 : ℝ) ≤ (16883642889218949/50000000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^2089 ≤ (16883642889218949/50000000000000000000 : ℝ)^512 := by
      have hnat : (7049 : ℕ)^2089*50000000000000000000^512 ≤ 16883642889218949^512*50000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 16883642889218949 50000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (16883642889218949/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (500139264641788839/500000000000000000 : ℝ) ≤ (10000682584983741/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (500139264641788839/500000000000000000 : ℝ)^512 ≤ (10000682584983741/10000000000000000 : ℝ)^2089 := by
      have hnat : (500139264641788839 : ℕ)^512*10000000000000000^2089 ≤ 10000682584983741^2089*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500139264641788839 500000000000000000 10000682584983741 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682584983741/10000000000000000 : ℝ)) (X := (500139264641788839/500000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023846874978660899/50000000000000000000 : ℝ) ≤ (5000584365850159/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50023846874978660899/50000000000000000000 : ℝ)^512 ≤ (5000584365850159/5000000000000000 : ℝ)^2089 := by
      have hnat : (50023846874978660899 : ℕ)^512*5000000000000000^2089 ≤ 5000584365850159^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023846874978660899 50000000000000000000 5000584365850159 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000584365850159/5000000000000000 : ℝ)) (X := (50023846874978660899/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016883642889218949/25000000000000000000 : ℝ) ≤ (2000330975683379/2000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (25016883642889218949/25000000000000000000 : ℝ)^512 ≤ (2000330975683379/2000000000000000 : ℝ)^2089 := by
      have hnat : (25016883642889218949 : ℕ)^512*2000000000000000^2089 ≤ 2000330975683379^2089*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016883642889218949 25000000000000000000 2000330975683379 2000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000330975683379/2000000000000000 : ℝ)) (X := (25016883642889218949/25000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(139264641788839/1000000000000000000 : ℝ) ≤ ((3928692168243467579/3930000000000000000 : ℝ)+2*(486146716577/275100000000000 : ℝ)*(11347/100000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (3928692168243467579/3930000000000000000 : ℝ)+2*(486146716577/275100000000000 : ℝ)*(11347/100000 : ℝ)=(10000682584983741/10000000000000000 : ℝ) by norm_num, show 1+2*(139264641788839/1000000000000000000 : ℝ)=(500139264641788839/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16883642889218949/50000000000000000000 : ℝ)+(139264641788839/1000000000000000000 : ℝ) ≤ ((3928692168243467579/3930000000000000000 : ℝ)+(486146716577/275100000000000 : ℝ)*((7049/50000 : ℝ)+(11347/100000 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (3928692168243467579/3930000000000000000 : ℝ)+(486146716577/275100000000000 : ℝ)*((7049/50000 : ℝ)+(11347/100000 : ℝ))=(5000584365850159/5000000000000000 : ℝ) by norm_num, show 1+(16883642889218949/50000000000000000000 : ℝ)+(139264641788839/1000000000000000000 : ℝ)=(50023846874978660899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16883642889218949/50000000000000000000 : ℝ) ≤ ((3928692168243467579/3930000000000000000 : ℝ)+2*(486146716577/275100000000000 : ℝ)*(7049/50000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (3928692168243467579/3930000000000000000 : ℝ)+2*(486146716577/275100000000000 : ℝ)*(7049/50000 : ℝ)=(2000330975683379/2000000000000000 : ℝ) by norm_num, show 1+2*(16883642889218949/50000000000000000000 : ℝ)=(25016883642889218949/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3928692168243467579/3930000000000000000 : ℝ)*(X 1 0+X 2 0)+(486146716577/275100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (3928692168243467579/3930000000000000000 : ℝ)) (alpha := (486146716577/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3928692168243467579/3930000000000000000 : ℝ)*(X 0 1+X 2 1)+(486146716577/275100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (3928692168243467579/3930000000000000000 : ℝ)) (alpha := (486146716577/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3928692168243467579/3930000000000000000 : ℝ)*(X 0 2+X 1 2)+(486146716577/275100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (3928692168243467579/3930000000000000000 : ℝ)) (alpha := (486146716577/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078190989/5000000000 : ℝ)*X 0 0+(26964713/50000000 : ℝ)*X 0 1+(2632899343/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267237519/500000000 : ℝ)*X 1 0+(-277608853/1250000000 : ℝ)*X 1 1+(5265798819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344750747/10000000000 : ℝ)*X 2 0+(5265798253/10000000000 : ℝ)*X 2 1+(-1110435543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436156827/1000000000 : ℝ)*X 0 0+(847275407/2000000000 : ℝ)*X 0 1+(70162817/156250000 : ℝ)*X 0 2+(436156827/1000000000 : ℝ)*X 1 0+(847275407/2000000000 : ℝ)*X 1 1+(70162817/156250000 : ℝ)*X 1 2+(436156827/1000000000 : ℝ)*X 2 0+(847275407/2000000000 : ℝ)*X 2 1+(70162817/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2156387257/10000000000 : ℝ)*X 0 0+(526611943/1000000000 : ℝ)*X 0 1+(1348155101/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328121533/2500000000 : ℝ)*X 1 0+(-523512233/2500000000 : ℝ)*X 1 1+(539262037/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20751899/39062500 : ℝ)*X 2 0+(215704813/400000000 : ℝ)*X 2 1+(-130878061/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180788751/5000000000 : ℝ)*X 0 0+(4489778449/10000000000 : ℝ)*X 0 1+(2118510887/5000000000 : ℝ)*X 0 2+(2180788751/5000000000 : ℝ)*X 1 0+(4489778449/10000000000 : ℝ)*X 1 1+(2118510887/5000000000 : ℝ)*X 1 2+(2180788751/5000000000 : ℝ)*X 2 0+(4489778449/10000000000 : ℝ)*X 2 1+(2118510887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140846735211161434515369873/13100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (791014371/100000000000000 : ℝ)*(base19) + (646702977/50000000000000 : ℝ)*(base23) + (138068423/50000000000000 : ℝ)*(lower2) + (174344841/50000000000000 : ℝ)*(upper3) + (8000069/3125000000000 : ℝ)*(lower4) + (1180151566180413/20000000000000 : ℝ)*(major0) + (1180151566180413/20000000000000 : ℝ)*(major1) + (1180151566180413/20000000000000 : ℝ)*(major2) + (3932562255175911/50000000000000 : ℝ)*(sp0) + (1966283500346903/25000000000000 : ℝ)*(sp1) + (7865133498996029/100000000000000 : ℝ)*(sp2) + (1968176983955607/50000000000000 : ℝ)*(sp3) + (10282050161/100000000000000 : ℝ)*(sp4) + (1658943893/6250000000000 : ℝ)*(sp7) + (1968190255506751/50000000000000 : ℝ)*(f.failure) + (7865134792401983/100000000000000 : ℝ)*(f.sum) + (588727125751/229250000000000000000000000 : ℝ)*base66 + (1514655617865336963/183400000000000000000000000000000 : ℝ)*base67 + (1554597891582136963/183400000000000000000000000000000 : ℝ)*base69 + (602224169819736963/183400000000000000000000000000000 : ℝ)*base71 + (335754695571/917000000000000000000000000 : ℝ)*base74 + (423451674570663037/183400000000000000000000000000000 : ℝ)*base76 + (1228748098470463037/183400000000000000000000000000000 : ℝ)*base78 + (3012301502121536963/183400000000000000000000000000000 : ℝ)*base79 + (3248906935917/917000000000000000000000000 : ℝ)*base81 + (185277/156250000000000000000 : ℝ)*base90 + (185277/156250000000000000000 : ℝ)*base92 + (185277/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145656921998050315856022183/65500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127618103/50000000000000 : ℝ)*(base19) + (342645411/100000000000000 : ℝ)*(base23) + (5929591/12500000000000 : ℝ)*(upper2) + (74475577/100000000000000 : ℝ)*(upper5) + (5930726120248841/100000000000000 : ℝ)*(major0) + (5930726120248841/100000000000000 : ℝ)*(major1) + (5930726120248841/100000000000000 : ℝ)*(major2) + (77147777/100000000000000 : ℝ)*(sp0) + (7230485583/100000000000000 : ℝ)*(sp1) + (9950389/250000000000 : ℝ)*(sp2) + (3952539904380589/50000000000000 : ℝ)*(sp4) + (3952536200093583/50000000000000 : ℝ)*(sp5) + (988134445388493/12500000000000 : ℝ)*(sp6) + (197818614023153/5000000000000 : ℝ)*(sp7) + (197818614023153/5000000000000 : ℝ)*(f.failure) + (1581015977181791/20000000000000 : ℝ)*(f.sum) + (122279856720083/13755000000000000000000000000 : ℝ)*base66 + (24137592674416481573/2751000000000000000000000000000000 : ℝ)*base67 + (16984765183222481573/2751000000000000000000000000000000 : ℝ)*base69 + (25862615774524481573/2751000000000000000000000000000000 : ℝ)*base71 + (51467086041923/13755000000000000000000000000 : ℝ)*base74 + (23197070734009481573/2751000000000000000000000000000000 : ℝ)*base75 + (10871295235840481573/2751000000000000000000000000000000 : ℝ)*base77 + (3897275619556481573/2751000000000000000000000000000000 : ℝ)*base79 + (83958660940223/13755000000000000000000000000 : ℝ)*base82 + (197119/15625000000000000000 : ℝ)*base89 + (197119/15625000000000000000 : ℝ)*base91 + (197119/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1164_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s7_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078204769/5000000000 : ℝ)*x 0 + (1348162767/2500000000 : ℝ)*x 1 + (2633035927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078204769/5000000000 : ℝ)^8357 ≤ (2621078263267/20000000000000 : ℝ)^6309 := by
    have hnat : (1078204769 : ℕ)^8357*20000000000000^6309 ≤ 2621078263267^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078204769 5000000000 2621078263267 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348162767/2500000000 : ℝ)^8357 ≤ (22065367551817/50000000000000 : ℝ)^6309 := by
    have hnat : (1348162767 : ℕ)^8357*50000000000000^6309 ≤ 22065367551817^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348162767 2500000000 22065367551817 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633035927/5000000000 : ℝ)^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309 := by
    have hnat : (2633035927 : ℕ)^8357*12500000000000^6309 ≤ 5345484196127^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633035927 5000000000 5345484196127 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078204769/5000000000 : ℝ), (1348162767/2500000000 : ℝ), (2633035927/5000000000 : ℝ)] ![(2621078263267/20000000000000 : ℝ), (22065367551817/50000000000000 : ℝ), (5345484196127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078204769/5000000000 : ℝ)|^8357 ≤ (2621078263267/20000000000000 : ℝ)^6309
        have hw : |(-1078204769/5000000000 : ℝ)|=(1078204769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348162767/2500000000 : ℝ)|^8357 ≤ (22065367551817/50000000000000 : ℝ)^6309
        have hw : |(1348162767/2500000000 : ℝ)|=(1348162767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633035927/5000000000 : ℝ)|^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309
        have hw : |(2633035927/5000000000 : ℝ)|=(2633035927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53446767/100000000 : ℝ)*x 0 + (-44412149/200000000 : ℝ)*x 1 + (2633035927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53446767/100000000 : ℝ)^8357 ≤ (87222892091/200000000000 : ℝ)^6309 := by
    have hnat : (53446767 : ℕ)^8357*200000000000^6309 ≤ 87222892091^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53446767 100000000 87222892091 200000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44412149/200000000 : ℝ)^8357 ≤ (2724936074241/20000000000000 : ℝ)^6309 := by
    have hnat : (44412149 : ℕ)^8357*20000000000000^6309 ≤ 2724936074241^6309*200000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44412149 200000000 2724936074241 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633035927/5000000000 : ℝ)^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309 := by
    have hnat : (2633035927 : ℕ)^8357*12500000000000^6309 ≤ 5345484196127^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633035927 5000000000 5345484196127 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53446767/100000000 : ℝ), (-44412149/200000000 : ℝ), (2633035927/5000000000 : ℝ)] ![(87222892091/200000000000 : ℝ), (2724936074241/20000000000000 : ℝ), (5345484196127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53446767/100000000 : ℝ)|^8357 ≤ (87222892091/200000000000 : ℝ)^6309
        have hw : |(53446767/100000000 : ℝ)|=(53446767/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44412149/200000000 : ℝ)|^8357 ≤ (2724936074241/20000000000000 : ℝ)^6309
        have hw : |(-44412149/200000000 : ℝ)|=(44412149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633035927/5000000000 : ℝ)|^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309
        have hw : |(2633035927/5000000000 : ℝ)|=(2633035927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53446767/100000000 : ℝ)*x 0 + (2633035927/5000000000 : ℝ)*x 1 + (-44412149/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53446767/100000000 : ℝ)^8357 ≤ (87222892091/200000000000 : ℝ)^6309 := by
    have hnat : (53446767 : ℕ)^8357*200000000000^6309 ≤ 87222892091^6309*100000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53446767 100000000 87222892091 200000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633035927/5000000000 : ℝ)^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309 := by
    have hnat : (2633035927 : ℕ)^8357*12500000000000^6309 ≤ 5345484196127^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633035927 5000000000 5345484196127 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44412149/200000000 : ℝ)^8357 ≤ (2724936074241/20000000000000 : ℝ)^6309 := by
    have hnat : (44412149 : ℕ)^8357*20000000000000^6309 ≤ 2724936074241^6309*200000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44412149 200000000 2724936074241 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53446767/100000000 : ℝ), (2633035927/5000000000 : ℝ), (-44412149/200000000 : ℝ)] ![(87222892091/200000000000 : ℝ), (5345484196127/12500000000000 : ℝ), (2724936074241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53446767/100000000 : ℝ)|^8357 ≤ (87222892091/200000000000 : ℝ)^6309
        have hw : |(53446767/100000000 : ℝ)|=(53446767/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633035927/5000000000 : ℝ)|^8357 ≤ (5345484196127/12500000000000 : ℝ)^6309
        have hw : |(2633035927/5000000000 : ℝ)|=(2633035927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44412149/200000000 : ℝ)|^8357 ≤ (2724936074241/20000000000000 : ℝ)^6309
        have hw : |(-44412149/200000000 : ℝ)|=(44412149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361582183/10000000000 : ℝ)*x 0 + (4236940431/10000000000 : ℝ)*x 1 + (4489853639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361582183/10000000000 : ℝ)^8357 ≤ (832926920433/2500000000000 : ℝ)^6309 := by
    have hnat : (4361582183 : ℕ)^8357*2500000000000^6309 ≤ 832926920433^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361582183 10000000000 832926920433 2500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236940431/10000000000 : ℝ)^8357 ≤ (32061787026729/100000000000000 : ℝ)^6309 := by
    have hnat : (4236940431 : ℕ)^8357*100000000000000^6309 ≤ 32061787026729^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236940431 10000000000 32061787026729 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489853639/10000000000 : ℝ)^8357 ≤ (34621136151687/100000000000000 : ℝ)^6309 := by
    have hnat : (4489853639 : ℕ)^8357*100000000000000^6309 ≤ 34621136151687^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489853639 10000000000 34621136151687 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361582183/10000000000 : ℝ), (4236940431/10000000000 : ℝ), (4489853639/10000000000 : ℝ)] ![(832926920433/2500000000000 : ℝ), (32061787026729/100000000000000 : ℝ), (34621136151687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361582183/10000000000 : ℝ)|^8357 ≤ (832926920433/2500000000000 : ℝ)^6309
        have hw : |(4361582183/10000000000 : ℝ)|=(4361582183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236940431/10000000000 : ℝ)|^8357 ≤ (32061787026729/100000000000000 : ℝ)^6309
        have hw : |(4236940431/10000000000 : ℝ)|=(4236940431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489853639/10000000000 : ℝ)|^8357 ≤ (34621136151687/100000000000000 : ℝ)^6309
        have hw : |(4489853639/10000000000 : ℝ)|=(4489853639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431282831/2000000000 : ℝ)*x 0 + (5266389861/10000000000 : ℝ)*x 1 + (1348083017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431282831/2000000000 : ℝ)^8357 ≤ (13105428484289/100000000000000 : ℝ)^6309 := by
    have hnat : (431282831 : ℕ)^8357*100000000000000^6309 ≤ 13105428484289^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431282831 2000000000 13105428484289 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266389861/10000000000 : ℝ)^8357 ≤ (5345911789613/12500000000000 : ℝ)^6309 := by
    have hnat : (5266389861 : ℕ)^8357*12500000000000^6309 ≤ 5345911789613^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266389861 10000000000 5345911789613 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348083017/2500000000 : ℝ)^8357 ≤ (2206363859067/5000000000000 : ℝ)^6309 := by
    have hnat : (1348083017 : ℕ)^8357*5000000000000^6309 ≤ 2206363859067^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348083017 2500000000 2206363859067 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431282831/2000000000 : ℝ), (5266389861/10000000000 : ℝ), (1348083017/2500000000 : ℝ)] ![(13105428484289/100000000000000 : ℝ), (5345911789613/12500000000000 : ℝ), (2206363859067/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431282831/2000000000 : ℝ)|^8357 ≤ (13105428484289/100000000000000 : ℝ)^6309
        have hw : |(-431282831/2000000000 : ℝ)|=(431282831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266389861/10000000000 : ℝ)|^8357 ≤ (5345911789613/12500000000000 : ℝ)^6309
        have hw : |(5266389861/10000000000 : ℝ)|=(5266389861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348083017/2500000000 : ℝ)|^8357 ≤ (2206363859067/5000000000000 : ℝ)^6309
        have hw : |(1348083017/2500000000 : ℝ)|=(1348083017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312555777/10000000000 : ℝ)*x 0 + (-2094348109/10000000000 : ℝ)*x 1 + (5392330979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312555777/10000000000 : ℝ)^8357 ≤ (43264603373869/100000000000000 : ℝ)^6309 := by
    have hnat : (5312555777 : ℕ)^8357*100000000000000^6309 ≤ 43264603373869^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312555777 10000000000 43264603373869 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094348109/10000000000 : ℝ)^8357 ≤ (6304065620801/50000000000000 : ℝ)^6309 := by
    have hnat : (2094348109 : ℕ)^8357*50000000000000^6309 ≤ 6304065620801^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094348109 10000000000 6304065620801 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392330979/10000000000 : ℝ)^8357 ≤ (44127265376823/100000000000000 : ℝ)^6309 := by
    have hnat : (5392330979 : ℕ)^8357*100000000000000^6309 ≤ 44127265376823^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392330979 10000000000 44127265376823 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312555777/10000000000 : ℝ), (-2094348109/10000000000 : ℝ), (5392330979/10000000000 : ℝ)] ![(43264603373869/100000000000000 : ℝ), (6304065620801/50000000000000 : ℝ), (44127265376823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312555777/10000000000 : ℝ)|^8357 ≤ (43264603373869/100000000000000 : ℝ)^6309
        have hw : |(5312555777/10000000000 : ℝ)|=(5312555777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094348109/10000000000 : ℝ)|^8357 ≤ (6304065620801/50000000000000 : ℝ)^6309
        have hw : |(-2094348109/10000000000 : ℝ)|=(2094348109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392330979/10000000000 : ℝ)|^8357 ≤ (44127265376823/100000000000000 : ℝ)^6309
        have hw : |(5392330979/10000000000 : ℝ)|=(5392330979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062511047/2000000000 : ℝ)*x 0 + (1348082963/2500000000 : ℝ)*x 1 + (-1047173827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062511047/2000000000 : ℝ)^8357 ≤ (43264597527067/100000000000000 : ℝ)^6309 := by
    have hnat : (1062511047 : ℕ)^8357*100000000000000^6309 ≤ 43264597527067^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062511047 2000000000 43264597527067 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348082963/2500000000 : ℝ)^8357 ≤ (11031818709987/25000000000000 : ℝ)^6309 := by
    have hnat : (1348082963 : ℕ)^8357*25000000000000^6309 ≤ 11031818709987^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348082963 2500000000 11031818709987 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047173827/5000000000 : ℝ)^8357 ≤ (6304063806651/50000000000000 : ℝ)^6309 := by
    have hnat : (1047173827 : ℕ)^8357*50000000000000^6309 ≤ 6304063806651^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047173827 5000000000 6304063806651 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062511047/2000000000 : ℝ), (1348082963/2500000000 : ℝ), (-1047173827/5000000000 : ℝ)] ![(43264597527067/100000000000000 : ℝ), (11031818709987/25000000000000 : ℝ), (6304063806651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062511047/2000000000 : ℝ)|^8357 ≤ (43264597527067/100000000000000 : ℝ)^6309
        have hw : |(1062511047/2000000000 : ℝ)|=(1062511047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348082963/2500000000 : ℝ)|^8357 ≤ (11031818709987/25000000000000 : ℝ)^6309
        have hw : |(1348082963/2500000000 : ℝ)|=(1348082963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047173827/5000000000 : ℝ)|^8357 ≤ (6304063806651/50000000000000 : ℝ)^6309
        have hw : |(-1047173827/5000000000 : ℝ)|=(1047173827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s7_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361591601/10000000000 : ℝ)*x 0 + (561152207/1250000000 : ℝ)*x 1 + (4237578959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361591601/10000000000 : ℝ)^8357 ≤ (33317172112633/100000000000000 : ℝ)^6309 := by
    have hnat : (4361591601 : ℕ)^8357*100000000000000^6309 ≤ 33317172112633^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361591601 10000000000 33317172112633 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561152207/1250000000 : ℝ)^8357 ≤ (6922928064703/20000000000000 : ℝ)^6309 := by
    have hnat : (561152207 : ℕ)^8357*20000000000000^6309 ≤ 6922928064703^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561152207 1250000000 6922928064703 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237578959/10000000000 : ℝ)^8357 ≤ (4008523444357/12500000000000 : ℝ)^6309 := by
    have hnat : (4237578959 : ℕ)^8357*12500000000000^6309 ≤ 4008523444357^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237578959 10000000000 4008523444357 12500000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361591601/10000000000 : ℝ), (561152207/1250000000 : ℝ), (4237578959/10000000000 : ℝ)] ![(33317172112633/100000000000000 : ℝ), (6922928064703/20000000000000 : ℝ), (4008523444357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361591601/10000000000 : ℝ)|^8357 ≤ (33317172112633/100000000000000 : ℝ)^6309
        have hw : |(4361591601/10000000000 : ℝ)|=(4361591601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561152207/1250000000 : ℝ)|^8357 ≤ (6922928064703/20000000000000 : ℝ)^6309
        have hw : |(561152207/1250000000 : ℝ)|=(561152207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237578959/10000000000 : ℝ)|^8357 ≤ (4008523444357/12500000000000 : ℝ)^6309
        have hw : |(4237578959/10000000000 : ℝ)|=(4237578959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (2089/512 : ℝ) ≤ (14067210296272767/100000000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^2089 ≤ (14067210296272767/100000000000000000000 : ℝ)^512 := by
      have hnat : (91 : ℕ)^2089*100000000000000000000^512 ≤ 14067210296272767^512*800^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 14067210296272767 100000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (14067210296272767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (2089/512 : ℝ) ≤ (16737534582326147/50000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^2089 ≤ (16737534582326147/50000000000000000000 : ℝ)^512 := by
      have hnat : (3517 : ℕ)^2089*50000000000000000000^512 ≤ 16737534582326147^512*25000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 16737534582326147 50000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (16737534582326147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014067210296272767/50000000000000000000 : ℝ) ≤ (10000689482713493/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (50014067210296272767/50000000000000000000 : ℝ)^512 ≤ (10000689482713493/10000000000000000 : ℝ)^2089 := by
      have hnat : (50014067210296272767 : ℕ)^512*10000000000000000^2089 ≤ 10000689482713493^2089*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014067210296272767 50000000000000000000 10000689482713493 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000689482713493/10000000000000000 : ℝ)) (X := (50014067210296272767/50000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047542279460925061/100000000000000000000 : ℝ) ≤ (5000582510296599/5000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (100047542279460925061/100000000000000000000 : ℝ)^512 ≤ (5000582510296599/5000000000000000 : ℝ)^2089 := by
      have hnat : (100047542279460925061 : ℕ)^512*5000000000000000^2089 ≤ 5000582510296599^2089*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047542279460925061 100000000000000000000 5000582510296599 5000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000582510296599/5000000000000000 : ℝ)) (X := (100047542279460925061/100000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016737534582326147/25000000000000000000 : ℝ) ≤ (10001640558472903/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (25016737534582326147/25000000000000000000 : ℝ)^512 ≤ (10001640558472903/10000000000000000 : ℝ)^2089 := by
      have hnat : (25016737534582326147 : ℕ)^512*10000000000000000^2089 ≤ 10001640558472903^2089*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016737534582326147 25000000000000000000 10001640558472903 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001640558472903/10000000000000000 : ℝ)) (X := (25016737534582326147/25000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14067210296272767/100000000000000000000 : ℝ) ≤ ((26921038290184147899/26930000000000000000 : ℝ)+2*(95107575941/53860000000000 : ℝ)*(91/800 : ℝ))^(2089/512 : ℝ) := by
    rw [show (26921038290184147899/26930000000000000000 : ℝ)+2*(95107575941/53860000000000 : ℝ)*(91/800 : ℝ)=(10000689482713493/10000000000000000 : ℝ) by norm_num, show 1+2*(14067210296272767/100000000000000000000 : ℝ)=(50014067210296272767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16737534582326147/50000000000000000000 : ℝ)+(14067210296272767/100000000000000000000 : ℝ) ≤ ((26921038290184147899/26930000000000000000 : ℝ)+(95107575941/53860000000000 : ℝ)*((3517/25000 : ℝ)+(91/800 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (26921038290184147899/26930000000000000000 : ℝ)+(95107575941/53860000000000 : ℝ)*((3517/25000 : ℝ)+(91/800 : ℝ))=(5000582510296599/5000000000000000 : ℝ) by norm_num, show 1+(16737534582326147/50000000000000000000 : ℝ)+(14067210296272767/100000000000000000000 : ℝ)=(100047542279460925061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16737534582326147/50000000000000000000 : ℝ) ≤ ((26921038290184147899/26930000000000000000 : ℝ)+2*(95107575941/53860000000000 : ℝ)*(3517/25000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (26921038290184147899/26930000000000000000 : ℝ)+2*(95107575941/53860000000000 : ℝ)*(3517/25000 : ℝ)=(10001640558472903/10000000000000000 : ℝ) by norm_num, show 1+2*(16737534582326147/50000000000000000000 : ℝ)=(25016737534582326147/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26921038290184147899/26930000000000000000 : ℝ)*(X 1 0+X 2 0)+(95107575941/53860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (91/800 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (26921038290184147899/26930000000000000000 : ℝ)) (alpha := (95107575941/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26921038290184147899/26930000000000000000 : ℝ)*(X 0 1+X 2 1)+(95107575941/53860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (91/800 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (26921038290184147899/26930000000000000000 : ℝ)) (alpha := (95107575941/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26921038290184147899/26930000000000000000 : ℝ)*(X 0 2+X 1 2)+(95107575941/53860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (91/800 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (26921038290184147899/26930000000000000000 : ℝ)) (alpha := (95107575941/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078204769/5000000000 : ℝ)*X 0 0+(1348162767/2500000000 : ℝ)*X 0 1+(2633035927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53446767/100000000 : ℝ)*X 1 0+(-44412149/200000000 : ℝ)*X 1 1+(2633035927/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53446767/100000000 : ℝ)*X 2 0+(2633035927/5000000000 : ℝ)*X 2 1+(-44412149/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361582183/10000000000 : ℝ)*X 0 0+(4236940431/10000000000 : ℝ)*X 0 1+(4489853639/10000000000 : ℝ)*X 0 2+(4361582183/10000000000 : ℝ)*X 1 0+(4236940431/10000000000 : ℝ)*X 1 1+(4489853639/10000000000 : ℝ)*X 1 2+(4361582183/10000000000 : ℝ)*X 2 0+(4236940431/10000000000 : ℝ)*X 2 1+(4489853639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431282831/2000000000 : ℝ)*X 0 0+(5266389861/10000000000 : ℝ)*X 0 1+(1348083017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312555777/10000000000 : ℝ)*X 1 0+(-2094348109/10000000000 : ℝ)*X 1 1+(5392330979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062511047/2000000000 : ℝ)*X 2 0+(1348082963/2500000000 : ℝ)*X 2 1+(-1047173827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361591601/10000000000 : ℝ)*X 0 0+(561152207/1250000000 : ℝ)*X 0 1+(4237578959/10000000000 : ℝ)*X 0 2+(4361591601/10000000000 : ℝ)*X 1 0+(561152207/1250000000 : ℝ)*X 1 1+(4237578959/10000000000 : ℝ)*X 1 2+(4361591601/10000000000 : ℝ)*X 2 0+(561152207/1250000000 : ℝ)*X 2 1+(4237578959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9463117333793289048699/1346500000000000000000000000 : ℝ) := by norm_num
    linear_combination (345816859/25000000000000 : ℝ)*(base19) + (1288265791/100000000000000 : ℝ)*(base23) + (50775307/100000000000000 : ℝ)*(lower2) + (177220419/100000000000000 : ℝ)*(upper3) + (26764043/25000000000000 : ℝ)*(upper5) + (296355834736511/5000000000000 : ℝ)*(major0) + (296355834736511/5000000000000 : ℝ)*(major1) + (296355834736511/5000000000000 : ℝ)*(major2) + (7900230885985977/100000000000000 : ℝ)*(sp0) + (316010693201211/4000000000000 : ℝ)*(sp1) + (7900267425031919/100000000000000 : ℝ)*(sp2) + (1976971992071339/50000000000000 : ℝ)*(sp3) + (18913655867/50000000000000 : ℝ)*(sp4) + (5114438867/25000000000000 : ℝ)*(sp7) + (1976982220949073/50000000000000 : ℝ)*(f.failure) + (790026871329771/10000000000000 : ℝ)*(f.sum) + (1153972245721/1346500000000000000000000000 : ℝ)*base65 + (517257890657340389/134650000000000000000000000000000 : ℝ)*base67 + (1280443579981859611/134650000000000000000000000000000 : ℝ)*base70 + (16785985030559611/134650000000000000000000000000000 : ℝ)*base72 + (1209105600697/168312500000000000000000000 : ℝ)*base73 + (854283707621140389/134650000000000000000000000000000 : ℝ)*base75 + (440730809850559611/134650000000000000000000000000000 : ℝ)*base78 + (2702424686392940389/134650000000000000000000000000000 : ℝ)*base79 + (470065444563/673250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1906471/156250000000000000000 : ℝ)*base90 + (1906471/156250000000000000000 : ℝ)*base92 + (1906471/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (717468685774759796181936747/168312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (434931431/100000000000000 : ℝ)*(base19) + (3460229/100000000000000 : ℝ)*(upper2) + (93921207/100000000000000 : ℝ)*(lower3) + (2776119/2500000000000 : ℝ)*(lower4) + (744637652283151/12500000000000 : ℝ)*(major0) + (744637652283151/12500000000000 : ℝ)*(major1) + (744637652283151/12500000000000 : ℝ)*(major2) + (45174040503/100000000000000 : ℝ)*(sp0) + (26398550467/100000000000000 : ℝ)*(sp2) + (5409285073/50000000000000 : ℝ)*(sp3) + (7940190079266013/100000000000000 : ℝ)*(sp4) + (1588046963675017/20000000000000 : ℝ)*(sp5) + (496263053422253/6250000000000 : ℝ)*(sp6) + (1986978111281571/50000000000000 : ℝ)*(sp7) + (1986983520566643/50000000000000 : ℝ)*(f.failure) + (1985058813326629/25000000000000 : ℝ)*(f.sum) + (1567432585809/538600000000000000000000000 : ℝ)*base65 + (2888697579666625251/336625000000000000000000000000000 : ℝ)*base68 + (2478987401791500251/336625000000000000000000000000000 : ℝ)*base70 + (3067608929865375251/336625000000000000000000000000000 : ℝ)*base72 + (3091559927681/2693000000000000000000000000 : ℝ)*base74 + (3856109695593874749/336625000000000000000000000000000 : ℝ)*base75 + (4126163549440249749/336625000000000000000000000000000 : ℝ)*base77 + (2358175003251750251/336625000000000000000000000000000 : ℝ)*base80 + (9860358375381/1346500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3665861/156250000000000000000 : ℝ)*base90 + (3665861/156250000000000000000 : ℝ)*base92 + (3665861/156250000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1164_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1164_s8_0 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078206899/5000000000 : ℝ)*x 0 + (5392591957/10000000000 : ℝ)*x 1 + (2633064117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078206899/5000000000 : ℝ)^8357 ≤ (13105425610353/100000000000000 : ℝ)^6309 := by
    have hnat : (1078206899 : ℕ)^8357*100000000000000^6309 ≤ 13105425610353^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078206899 5000000000 13105425610353 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392591957/10000000000 : ℝ)^8357 ≤ (44130094342369/100000000000000 : ℝ)^6309 := by
    have hnat : (5392591957 : ℕ)^8357*100000000000000^6309 ≤ 44130094342369^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392591957 10000000000 44130094342369 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633064117/5000000000 : ℝ)^8357 ≤ (10691120008579/25000000000000 : ℝ)^6309 := by
    have hnat : (2633064117 : ℕ)^8357*25000000000000^6309 ≤ 10691120008579^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633064117 5000000000 10691120008579 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078206899/5000000000 : ℝ), (5392591957/10000000000 : ℝ), (2633064117/5000000000 : ℝ)] ![(13105425610353/100000000000000 : ℝ), (44130094342369/100000000000000 : ℝ), (10691120008579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078206899/5000000000 : ℝ)|^8357 ≤ (13105425610353/100000000000000 : ℝ)^6309
        have hw : |(-1078206899/5000000000 : ℝ)|=(1078206899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392591957/10000000000 : ℝ)|^8357 ≤ (44130094342369/100000000000000 : ℝ)^6309
        have hw : |(5392591957/10000000000 : ℝ)|=(5392591957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633064117/5000000000 : ℝ)|^8357 ≤ (10691120008579/25000000000000 : ℝ)^6309
        have hw : |(2633064117/5000000000 : ℝ)|=(2633064117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_1 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344662053/10000000000 : ℝ)*x 0 + (-2220552333/10000000000 : ℝ)*x 1 + (2633064107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344662053/10000000000 : ℝ)^8357 ≤ (43611287732197/100000000000000 : ℝ)^6309 := by
    have hnat : (5344662053 : ℕ)^8357*100000000000000^6309 ≤ 43611287732197^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344662053 10000000000 43611287732197 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220552333/10000000000 : ℝ)^8357 ≤ (13624232422561/100000000000000 : ℝ)^6309 := by
    have hnat : (2220552333 : ℕ)^8357*100000000000000^6309 ≤ 13624232422561^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220552333 10000000000 13624232422561 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633064107/5000000000 : ℝ)^8357 ≤ (42764479819181/100000000000000 : ℝ)^6309 := by
    have hnat : (2633064107 : ℕ)^8357*100000000000000^6309 ≤ 42764479819181^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633064107 5000000000 42764479819181 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344662053/10000000000 : ℝ), (-2220552333/10000000000 : ℝ), (2633064107/5000000000 : ℝ)] ![(43611287732197/100000000000000 : ℝ), (13624232422561/100000000000000 : ℝ), (42764479819181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344662053/10000000000 : ℝ)|^8357 ≤ (43611287732197/100000000000000 : ℝ)^6309
        have hw : |(5344662053/10000000000 : ℝ)|=(5344662053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2220552333/10000000000 : ℝ)|^8357 ≤ (13624232422561/100000000000000 : ℝ)^6309
        have hw : |(-2220552333/10000000000 : ℝ)|=(2220552333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633064107/5000000000 : ℝ)|^8357 ≤ (42764479819181/100000000000000 : ℝ)^6309
        have hw : |(2633064107/5000000000 : ℝ)|=(2633064107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_2 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668082757/1250000000 : ℝ)*x 0 + (210645129/400000000 : ℝ)*x 1 + (-444110463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668082757/1250000000 : ℝ)^8357 ≤ (43611287764623/100000000000000 : ℝ)^6309 := by
    have hnat : (668082757 : ℕ)^8357*100000000000000^6309 ≤ 43611287764623^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668082757 1250000000 43611287764623 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210645129/400000000 : ℝ)^8357 ≤ (21382239968753/50000000000000 : ℝ)^6309 := by
    have hnat : (210645129 : ℕ)^8357*50000000000000^6309 ≤ 21382239968753^6309*400000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210645129 400000000 21382239968753 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444110463/2000000000 : ℝ)^8357 ≤ (13624232276271/100000000000000 : ℝ)^6309 := by
    have hnat : (444110463 : ℕ)^8357*100000000000000^6309 ≤ 13624232276271^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444110463 2000000000 13624232276271 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668082757/1250000000 : ℝ), (210645129/400000000 : ℝ), (-444110463/2000000000 : ℝ)] ![(43611287764623/100000000000000 : ℝ), (21382239968753/50000000000000 : ℝ), (13624232276271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668082757/1250000000 : ℝ)|^8357 ≤ (43611287764623/100000000000000 : ℝ)^6309
        have hw : |(668082757/1250000000 : ℝ)|=(668082757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210645129/400000000 : ℝ)|^8357 ≤ (21382239968753/50000000000000 : ℝ)^6309
        have hw : |(210645129/400000000 : ℝ)|=(210645129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-444110463/2000000000 : ℝ)|^8357 ≤ (13624232276271/100000000000000 : ℝ)^6309
        have hw : |(-444110463/2000000000 : ℝ)|=(444110463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_3 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361585101/10000000000 : ℝ)*x 0 + (847411073/2000000000 : ℝ)*x 1 + (1122434489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361585101/10000000000 : ℝ)^8357 ≤ (33317106342873/100000000000000 : ℝ)^6309 := by
    have hnat : (4361585101 : ℕ)^8357*100000000000000^6309 ≤ 33317106342873^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361585101 10000000000 33317106342873 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847411073/2000000000 : ℝ)^8357 ≤ (1603146954413/5000000000000 : ℝ)^6309 := by
    have hnat : (847411073 : ℕ)^8357*5000000000000^6309 ≤ 1603146954413^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847411073 2000000000 1603146954413 5000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122434489/2500000000 : ℝ)^8357 ≤ (1081873580059/3125000000000 : ℝ)^6309 := by
    have hnat : (1122434489 : ℕ)^8357*3125000000000^6309 ≤ 1081873580059^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122434489 2500000000 1081873580059 3125000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361585101/10000000000 : ℝ), (847411073/2000000000 : ℝ), (1122434489/2500000000 : ℝ)] ![(33317106342873/100000000000000 : ℝ), (1603146954413/5000000000000 : ℝ), (1081873580059/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361585101/10000000000 : ℝ)|^8357 ≤ (33317106342873/100000000000000 : ℝ)^6309
        have hw : |(4361585101/10000000000 : ℝ)|=(4361585101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847411073/2000000000 : ℝ)|^8357 ≤ (1603146954413/5000000000000 : ℝ)^6309
        have hw : |(847411073/2000000000 : ℝ)|=(847411073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122434489/2500000000 : ℝ)|^8357 ≤ (1081873580059/3125000000000 : ℝ)^6309
        have hw : |(1122434489/2500000000 : ℝ)|=(1122434489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_4 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078209199/5000000000 : ℝ)*x 0 + (658305689/1250000000 : ℝ)*x 1 + (5392273691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078209199/5000000000 : ℝ)^8357 ≤ (3276365660369/25000000000000 : ℝ)^6309 := by
    have hnat : (1078209199 : ℕ)^8357*25000000000000^6309 ≤ 3276365660369^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078209199 5000000000 3276365660369 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658305689/1250000000 : ℝ)^8357 ≤ (21383946476129/50000000000000 : ℝ)^6309 := by
    have hnat : (658305689 : ℕ)^8357*50000000000000^6309 ≤ 21383946476129^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658305689 1250000000 21383946476129 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392273691/10000000000 : ℝ)^8357 ≤ (11031661097187/25000000000000 : ℝ)^6309 := by
    have hnat : (5392273691 : ℕ)^8357*25000000000000^6309 ≤ 11031661097187^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392273691 10000000000 11031661097187 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078209199/5000000000 : ℝ), (658305689/1250000000 : ℝ), (5392273691/10000000000 : ℝ)] ![(3276365660369/25000000000000 : ℝ), (21383946476129/50000000000000 : ℝ), (11031661097187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078209199/5000000000 : ℝ)|^8357 ≤ (3276365660369/25000000000000 : ℝ)^6309
        have hw : |(-1078209199/5000000000 : ℝ)|=(1078209199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658305689/1250000000 : ℝ)|^8357 ≤ (21383946476129/50000000000000 : ℝ)^6309
        have hw : |(658305689/1250000000 : ℝ)|=(658305689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392273691/10000000000 : ℝ)|^8357 ≤ (11031661097187/25000000000000 : ℝ)^6309
        have hw : |(5392273691/10000000000 : ℝ)|=(5392273691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_5 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328142659/2500000000 : ℝ)*x 0 + (-2094407591/10000000000 : ℝ)*x 1 + (5392272433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328142659/2500000000 : ℝ)^8357 ≤ (43264763664773/100000000000000 : ℝ)^6309 := by
    have hnat : (1328142659 : ℕ)^8357*100000000000000^6309 ≤ 43264763664773^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328142659 2500000000 43264763664773 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094407591/10000000000 : ℝ)^8357 ≤ (12608605570179/100000000000000 : ℝ)^6309 := by
    have hnat : (2094407591 : ℕ)^8357*100000000000000^6309 ≤ 12608605570179^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094407591 10000000000 12608605570179 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392272433/10000000000 : ℝ)^8357 ≤ (11031657688089/25000000000000 : ℝ)^6309 := by
    have hnat : (5392272433 : ℕ)^8357*25000000000000^6309 ≤ 11031657688089^6309*10000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392272433 10000000000 11031657688089 25000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328142659/2500000000 : ℝ), (-2094407591/10000000000 : ℝ), (5392272433/10000000000 : ℝ)] ![(43264763664773/100000000000000 : ℝ), (12608605570179/100000000000000 : ℝ), (11031657688089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328142659/2500000000 : ℝ)|^8357 ≤ (43264763664773/100000000000000 : ℝ)^6309
        have hw : |(1328142659/2500000000 : ℝ)|=(1328142659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094407591/10000000000 : ℝ)|^8357 ≤ (12608605570179/100000000000000 : ℝ)^6309
        have hw : |(-2094407591/10000000000 : ℝ)|=(2094407591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392272433/10000000000 : ℝ)|^8357 ≤ (11031657688089/25000000000000 : ℝ)^6309
        have hw : |(5392272433/10000000000 : ℝ)|=(5392272433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_6 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062513953/2000000000 : ℝ)*x 0 + (2696136707/5000000000 : ℝ)*x 1 + (-523601859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062513953/2000000000 : ℝ)^8357 ≤ (4326475426889/10000000000000 : ℝ)^6309 := by
    have hnat : (1062513953 : ℕ)^8357*10000000000000^6309 ≤ 4326475426889^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062513953 2000000000 4326475426889 10000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696136707/5000000000 : ℝ)^8357 ≤ (44126641386141/100000000000000 : ℝ)^6309 := by
    have hnat : (2696136707 : ℕ)^8357*100000000000000^6309 ≤ 44126641386141^6309*5000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696136707 5000000000 44126641386141 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523601859/2500000000 : ℝ)^8357 ≤ (6304302167077/50000000000000 : ℝ)^6309 := by
    have hnat : (523601859 : ℕ)^8357*50000000000000^6309 ≤ 6304302167077^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523601859 2500000000 6304302167077 50000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062513953/2000000000 : ℝ), (2696136707/5000000000 : ℝ), (-523601859/2500000000 : ℝ)] ![(4326475426889/10000000000000 : ℝ), (44126641386141/100000000000000 : ℝ), (6304302167077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062513953/2000000000 : ℝ)|^8357 ≤ (4326475426889/10000000000000 : ℝ)^6309
        have hw : |(1062513953/2000000000 : ℝ)|=(1062513953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696136707/5000000000 : ℝ)|^8357 ≤ (44126641386141/100000000000000 : ℝ)^6309
        have hw : |(2696136707/5000000000 : ℝ)|=(2696136707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523601859/2500000000 : ℝ)|^8357 ≤ (6304302167077/50000000000000 : ℝ)^6309
        have hw : |(-523601859/2500000000 : ℝ)|=(523601859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1164_s8_7 (p : ℝ) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545199373/1250000000 : ℝ)*x 0 + (1122275657/2500000000 : ℝ)*x 1 + (847538549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545199373/1250000000 : ℝ)^8357 ≤ (33317206343277/100000000000000 : ℝ)^6309 := by
    have hnat : (545199373 : ℕ)^8357*100000000000000^6309 ≤ 33317206343277^6309*1250000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545199373 1250000000 33317206343277 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122275657/2500000000 : ℝ)^8357 ≤ (6922693095581/20000000000000 : ℝ)^6309 := by
    have hnat : (1122275657 : ℕ)^8357*20000000000000^6309 ≤ 6922693095581^6309*2500000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122275657 2500000000 6922693095581 20000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847538549/2000000000 : ℝ)^8357 ≤ (32069328164947/100000000000000 : ℝ)^6309 := by
    have hnat : (847538549 : ℕ)^8357*100000000000000^6309 ≤ 32069328164947^6309*2000000000^8357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847538549 2000000000 32069328164947 100000000000000 8357 6309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8357/2048 : ℝ)) 8357 6309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545199373/1250000000 : ℝ), (1122275657/2500000000 : ℝ), (847538549/2000000000 : ℝ)] ![(33317206343277/100000000000000 : ℝ), (6922693095581/20000000000000 : ℝ), (32069328164947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545199373/1250000000 : ℝ)|^8357 ≤ (33317206343277/100000000000000 : ℝ)^6309
        have hw : |(545199373/1250000000 : ℝ)|=(545199373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122275657/2500000000 : ℝ)|^8357 ≤ (6922693095581/20000000000000 : ℝ)^6309
        have hw : |(1122275657/2500000000 : ℝ)|=(1122275657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847538549/2000000000 : ℝ)|^8357 ≤ (32069328164947/100000000000000 : ℝ)^6309
        have hw : |(847538549/2000000000 : ℝ)|=(847538549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1164_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (2089/512 : ℝ) ≤ (7048754675495621/50000000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^2089 ≤ (7048754675495621/50000000000000000000 : ℝ)^512 := by
      have hnat : (11381 : ℕ)^2089*50000000000000000000^512 ≤ 7048754675495621^512*100000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 7048754675495621 50000000000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (7048754675495621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (2089/512 : ℝ) ≤ (522138370020007/1562500000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^2089 ≤ (522138370020007/1562500000000000000 : ℝ)^512 := by
      have hnat : (7031 : ℕ)^2089*1562500000000000000^512 ≤ 522138370020007^512*50000^2089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 522138370020007 1562500000000000000 2089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (522138370020007/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007048754675495621/25000000000000000000 : ℝ) ≤ (10000690967617129/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (25007048754675495621/25000000000000000000 : ℝ)^512 ≤ (10000690967617129/10000000000000000 : ℝ)^2089 := by
      have hnat : (25007048754675495621 : ℕ)^512*10000000000000000^2089 ≤ 10000690967617129^2089*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007048754675495621 25000000000000000000 10000690967617129 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690967617129/10000000000000000 : ℝ)) (X := (25007048754675495621/25000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004751436503227169/10000000000000000000 : ℝ) ≤ (10001164336674497/10000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (10004751436503227169/10000000000000000000 : ℝ)^512 ≤ (10001164336674497/10000000000000000 : ℝ)^2089 := by
      have hnat : (10004751436503227169 : ℕ)^512*10000000000000000^2089 ≤ 10001164336674497^2089*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004751436503227169 10000000000000000000 10001164336674497 10000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001164336674497/10000000000000000 : ℝ)) (X := (10004751436503227169/10000000000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (781772138370020007/781250000000000000 : ℝ) ≤ (2000327541146373/2000000000000000 : ℝ) ^ (2089/512 : ℝ) := by
    have hpowers : (781772138370020007/781250000000000000 : ℝ)^512 ≤ (2000327541146373/2000000000000000 : ℝ)^2089 := by
      have hnat : (781772138370020007 : ℕ)^512*2000000000000000^2089 ≤ 2000327541146373^2089*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781772138370020007 781250000000000000 2000327541146373 2000000000000000 512 2089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000327541146373/2000000000000000 : ℝ)) (X := (781772138370020007/781250000000000000 : ℝ)) (by norm_num) 2089 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7048754675495621/50000000000000000000 : ℝ) ≤ ((26801077657697712433/26810000000000000000 : ℝ)+2*(59171132171/33512500000000 : ℝ)*(11381/100000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (26801077657697712433/26810000000000000000 : ℝ)+2*(59171132171/33512500000000 : ℝ)*(11381/100000 : ℝ)=(10000690967617129/10000000000000000 : ℝ) by norm_num, show 1+2*(7048754675495621/50000000000000000000 : ℝ)=(25007048754675495621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(522138370020007/1562500000000000000 : ℝ)+(7048754675495621/50000000000000000000 : ℝ) ≤ ((26801077657697712433/26810000000000000000 : ℝ)+(59171132171/33512500000000 : ℝ)*((7031/50000 : ℝ)+(11381/100000 : ℝ)))^(2089/512 : ℝ) := by
    rw [show (26801077657697712433/26810000000000000000 : ℝ)+(59171132171/33512500000000 : ℝ)*((7031/50000 : ℝ)+(11381/100000 : ℝ))=(10001164336674497/10000000000000000 : ℝ) by norm_num, show 1+(522138370020007/1562500000000000000 : ℝ)+(7048754675495621/50000000000000000000 : ℝ)=(10004751436503227169/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(522138370020007/1562500000000000000 : ℝ) ≤ ((26801077657697712433/26810000000000000000 : ℝ)+2*(59171132171/33512500000000 : ℝ)*(7031/50000 : ℝ))^(2089/512 : ℝ) := by
    rw [show (26801077657697712433/26810000000000000000 : ℝ)+2*(59171132171/33512500000000 : ℝ)*(7031/50000 : ℝ)=(2000327541146373/2000000000000000 : ℝ) by norm_num, show 1+2*(522138370020007/1562500000000000000 : ℝ)=(781772138370020007/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26801077657697712433/26810000000000000000 : ℝ)*(X 1 0+X 2 0)+(59171132171/33512500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (26801077657697712433/26810000000000000000 : ℝ)) (alpha := (59171132171/33512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26801077657697712433/26810000000000000000 : ℝ)*(X 0 1+X 2 1)+(59171132171/33512500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (26801077657697712433/26810000000000000000 : ℝ)) (alpha := (59171132171/33512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26801077657697712433/26810000000000000000 : ℝ)*(X 0 2+X 1 2)+(59171132171/33512500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2089/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (26801077657697712433/26810000000000000000 : ℝ)) (alpha := (59171132171/33512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078206899/5000000000 : ℝ)*X 0 0+(5392591957/10000000000 : ℝ)*X 0 1+(2633064117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344662053/10000000000 : ℝ)*X 1 0+(-2220552333/10000000000 : ℝ)*X 1 1+(2633064107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668082757/1250000000 : ℝ)*X 2 0+(210645129/400000000 : ℝ)*X 2 1+(-444110463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361585101/10000000000 : ℝ)*X 0 0+(847411073/2000000000 : ℝ)*X 0 1+(1122434489/2500000000 : ℝ)*X 0 2+(4361585101/10000000000 : ℝ)*X 1 0+(847411073/2000000000 : ℝ)*X 1 1+(1122434489/2500000000 : ℝ)*X 1 2+(4361585101/10000000000 : ℝ)*X 2 0+(847411073/2000000000 : ℝ)*X 2 1+(1122434489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078209199/5000000000 : ℝ)*X 0 0+(658305689/1250000000 : ℝ)*X 0 1+(5392273691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328142659/2500000000 : ℝ)*X 1 0+(-2094407591/10000000000 : ℝ)*X 1 1+(5392272433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062513953/2000000000 : ℝ)*X 2 0+(2696136707/5000000000 : ℝ)*X 2 1+(-523601859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545199373/1250000000 : ℝ)*X 0 0+(1122275657/2500000000 : ℝ)*X 0 1+(847538549/2000000000 : ℝ)*X 0 2+(545199373/1250000000 : ℝ)*X 1 0+(1122275657/2500000000 : ℝ)*X 1 1+(847538549/2000000000 : ℝ)*X 1 2+(545199373/1250000000 : ℝ)*X 2 0+(1122275657/2500000000 : ℝ)*X 2 1+(847538549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1164_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426116550820865157983476167/47875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1734584099/100000000000000 : ℝ)*(base19) + (1634961107/100000000000000 : ℝ)*(base23) + (13904343/25000000000000 : ℝ)*(lower2) + (204029489/100000000000000 : ℝ)*(upper3) + (157460463/100000000000000 : ℝ)*(upper5) + (1483135811990623/25000000000000 : ℝ)*(major0) + (1483135811990623/25000000000000 : ℝ)*(major1) + (1483135811990623/25000000000000 : ℝ)*(major2) + (988431756434127/12500000000000 : ℝ)*(sp0) + (1581499996584813/20000000000000 : ℝ)*(sp1) + (7907500082547057/100000000000000 : ℝ)*(sp2) + (989389629682873/25000000000000 : ℝ)*(sp3) + (11916508787/25000000000000 : ℝ)*(sp4) + (1038519937/4000000000000 : ℝ)*(sp7) + (989396120432479/25000000000000 : ℝ)*(f.failure) + (1976875429377041/25000000000000 : ℝ)*(f.sum) + (2777973188323/478750000000000000000000000 : ℝ)*base66 + (312917947674416537/95750000000000000000000000000000 : ℝ)*base67 + (1850006253863666537/95750000000000000000000000000000 : ℝ)*base69 + (518990832542666537/95750000000000000000000000000000 : ℝ)*base71 + (12423952351017/1915000000000000000000000000 : ℝ)*base74 + (391959254880166537/95750000000000000000000000000000 : ℝ)*base75 + (21439003767416537/95750000000000000000000000000000 : ℝ)*base77 + (633163805856666537/95750000000000000000000000000000 : ℝ)*base79 + (248057835439/957500000000000000000000000 : ℝ)*base81 + (676433/78125000000000000000 : ℝ)*base90 + (676433/78125000000000000000 : ℝ)*base92 + (676433/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1704256307219652989411077899/335125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (700509583/50000000000000 : ℝ)*(base19) + (371883909/50000000000000 : ℝ)*(base23) + (124110773/100000000000000 : ℝ)*(lower1) + (9480521/3125000000000 : ℝ)*(lower4) + (134888197/100000000000000 : ℝ)*(upper5) + (2981237064245599/50000000000000 : ℝ)*(major0) + (2981237064245599/50000000000000 : ℝ)*(major1) + (2981237064245599/50000000000000 : ℝ)*(major2) + (18959930719/50000000000000 : ℝ)*(sp0) + (12361879267/100000000000000 : ℝ)*(sp2) + (397367943587709/5000000000000 : ℝ)*(sp4) + (1986848847649113/25000000000000 : ℝ)*(sp5) + (7947383685968533/100000000000000 : ℝ)*(sp6) + (1988775647926137/50000000000000 : ℝ)*(sp7) + (1988775647926137/50000000000000 : ℝ)*(f.failure) + (3973698395807809/50000000000000 : ℝ)*(f.sum) + (6707561388049/3351250000000000000000000000 : ℝ)*base66 + (424170328426852519/191500000000000000000000000000000 : ℝ)*base68 + (1662873155907147481/191500000000000000000000000000000 : ℝ)*base69 + (2294936890438147481/191500000000000000000000000000000 : ℝ)*base71 + (9321672073459/3351250000000000000000000000 : ℝ)*base74 + (3636416842281147481/191500000000000000000000000000000 : ℝ)*base75 + (2117949866350647481/191500000000000000000000000000000 : ℝ)*base77 + (1225410975866647481/191500000000000000000000000000000 : ℝ)*base79 + (69547425772879/13405000000000000000000000000 : ℝ)*base81 + (2104199/156250000000000000000 : ℝ)*base90 + (2104199/156250000000000000000 : ℝ)*base92 + (2104199/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1164_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1164_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1164_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1164_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1164_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1164_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2089/512 : ℝ) ≤ p) (hpb : p ≤ (8357/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4684473/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1164_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
