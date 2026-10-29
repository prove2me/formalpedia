-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:53.560162+00:00
-- url     : https://prove2.me/submissions/6d729a8f-7b4d-4172-b19e-16c199b73a55

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
theorem support_rectangle_w1401_s0_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55461757/312500000 : ℝ)*x 0 + (186619423/312500000 : ℝ)*x 1 + (4824789413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55461757/312500000 : ℝ)^4361 ≤ (2610201144817/25000000000000 : ℝ)^3337 := by
    have hnat : (55461757 : ℕ)^4361*25000000000000^3337 ≤ 2610201144817^3337*312500000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55461757 312500000 2610201144817 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186619423/312500000 : ℝ)^4361 ≤ (3186268925997/6250000000000 : ℝ)^3337 := by
    have hnat : (186619423 : ℕ)^4361*6250000000000^3337 ≤ 3186268925997^3337*312500000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186619423 312500000 3186268925997 6250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824789413/10000000000 : ℝ)^4361 ≤ (1928944629003/5000000000000 : ℝ)^3337 := by
    have hnat : (4824789413 : ℕ)^4361*5000000000000^3337 ≤ 1928944629003^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824789413 10000000000 1928944629003 5000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55461757/312500000 : ℝ), (186619423/312500000 : ℝ), (4824789413/10000000000 : ℝ)] ![(2610201144817/25000000000000 : ℝ), (3186268925997/6250000000000 : ℝ), (1928944629003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55461757/312500000 : ℝ)|^4361 ≤ (2610201144817/25000000000000 : ℝ)^3337
        have hw : |(-55461757/312500000 : ℝ)|=(55461757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186619423/312500000 : ℝ)|^4361 ≤ (3186268925997/6250000000000 : ℝ)^3337
        have hw : |(186619423/312500000 : ℝ)|=(186619423/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824789413/10000000000 : ℝ)|^4361 ≤ (1928944629003/5000000000000 : ℝ)^3337
        have hw : |(4824789413/10000000000 : ℝ)|=(4824789413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1373804449/2500000000 : ℝ)*x 0 + (-2423999043/10000000000 : ℝ)*x 1 + (4824789657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373804449/2500000000 : ℝ)^4361 ≤ (11432364180061/25000000000000 : ℝ)^3337 := by
    have hnat : (1373804449 : ℕ)^4361*25000000000000^3337 ≤ 11432364180061^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373804449 2500000000 11432364180061 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423999043/10000000000 : ℝ)^4361 ≤ (61295500533/390625000000 : ℝ)^3337 := by
    have hnat : (2423999043 : ℕ)^4361*390625000000^3337 ≤ 61295500533^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423999043 10000000000 61295500533 390625000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824789657/10000000000 : ℝ)^4361 ≤ (9644723782443/25000000000000 : ℝ)^3337 := by
    have hnat : (4824789657 : ℕ)^4361*25000000000000^3337 ≤ 9644723782443^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824789657 10000000000 9644723782443 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373804449/2500000000 : ℝ), (-2423999043/10000000000 : ℝ), (4824789657/10000000000 : ℝ)] ![(11432364180061/25000000000000 : ℝ), (61295500533/390625000000 : ℝ), (9644723782443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373804449/2500000000 : ℝ)|^4361 ≤ (11432364180061/25000000000000 : ℝ)^3337
        have hw : |(1373804449/2500000000 : ℝ)|=(1373804449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2423999043/10000000000 : ℝ)|^4361 ≤ (61295500533/390625000000 : ℝ)^3337
        have hw : |(-2423999043/10000000000 : ℝ)|=(2423999043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824789657/10000000000 : ℝ)|^4361 ≤ (9644723782443/25000000000000 : ℝ)^3337
        have hw : |(4824789657/10000000000 : ℝ)|=(4824789657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099043593/2000000000 : ℝ)*x 0 + (4824789563/10000000000 : ℝ)*x 1 + (-1211999471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099043593/2000000000 : ℝ)^4361 ≤ (45729458558169/100000000000000 : ℝ)^3337 := by
    have hnat : (1099043593 : ℕ)^4361*100000000000000^3337 ≤ 45729458558169^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099043593 2000000000 45729458558169 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824789563/10000000000 : ℝ)^4361 ≤ (19289447073753/50000000000000 : ℝ)^3337 := by
    have hnat : (4824789563 : ℕ)^4361*50000000000000^3337 ≤ 19289447073753^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824789563 10000000000 19289447073753 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211999471/5000000000 : ℝ)^4361 ≤ (15691647281997/100000000000000 : ℝ)^3337 := by
    have hnat : (1211999471 : ℕ)^4361*100000000000000^3337 ≤ 15691647281997^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211999471 5000000000 15691647281997 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099043593/2000000000 : ℝ), (4824789563/10000000000 : ℝ), (-1211999471/5000000000 : ℝ)] ![(45729458558169/100000000000000 : ℝ), (19289447073753/50000000000000 : ℝ), (15691647281997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099043593/2000000000 : ℝ)|^4361 ≤ (45729458558169/100000000000000 : ℝ)^3337
        have hw : |(1099043593/2000000000 : ℝ)|=(1099043593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824789563/10000000000 : ℝ)|^4361 ≤ (19289447073753/50000000000000 : ℝ)^3337
        have hw : |(4824789563/10000000000 : ℝ)|=(4824789563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1211999471/5000000000 : ℝ)|^4361 ≤ (15691647281997/100000000000000 : ℝ)^3337
        have hw : |(-1211999471/5000000000 : ℝ)|=(1211999471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2085021939/5000000000 : ℝ)*x 0 + (3104154639/10000000000 : ℝ)*x 1 + (5560135507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085021939/5000000000 : ℝ)^4361 ≤ (6376847650189/20000000000000 : ℝ)^3337 := by
    have hnat : (2085021939 : ℕ)^4361*20000000000000^3337 ≤ 6376847650189^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085021939 5000000000 6376847650189 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104154639/10000000000 : ℝ)^4361 ≤ (1083951480961/5000000000000 : ℝ)^3337 := by
    have hnat : (3104154639 : ℕ)^4361*5000000000000^3337 ≤ 1083951480961^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104154639 10000000000 1083951480961 5000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5560135507/10000000000 : ℝ)^4361 ≤ (5804591513981/12500000000000 : ℝ)^3337 := by
    have hnat : (5560135507 : ℕ)^4361*12500000000000^3337 ≤ 5804591513981^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560135507 10000000000 5804591513981 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085021939/5000000000 : ℝ), (3104154639/10000000000 : ℝ), (5560135507/10000000000 : ℝ)] ![(6376847650189/20000000000000 : ℝ), (1083951480961/5000000000000 : ℝ), (5804591513981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085021939/5000000000 : ℝ)|^4361 ≤ (6376847650189/20000000000000 : ℝ)^3337
        have hw : |(2085021939/5000000000 : ℝ)|=(2085021939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104154639/10000000000 : ℝ)|^4361 ≤ (1083951480961/5000000000000 : ℝ)^3337
        have hw : |(3104154639/10000000000 : ℝ)|=(3104154639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5560135507/10000000000 : ℝ)|^4361 ≤ (5804591513981/12500000000000 : ℝ)^3337
        have hw : |(5560135507/10000000000 : ℝ)|=(5560135507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1778931283/10000000000 : ℝ)*x 0 + (606774753/1250000000 : ℝ)*x 1 + (5941362107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1778931283/10000000000 : ℝ)^4361 ≤ (5236380323403/50000000000000 : ℝ)^3337 := by
    have hnat : (1778931283 : ℕ)^4361*50000000000000^3337 ≤ 5236380323403^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778931283 10000000000 5236380323403 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606774753/1250000000 : ℝ)^4361 ≤ (7777297787/20000000000 : ℝ)^3337 := by
    have hnat : (606774753 : ℕ)^4361*20000000000^3337 ≤ 7777297787^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606774753 1250000000 7777297787 20000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5941362107/10000000000 : ℝ)^4361 ≤ (5064075040149/10000000000000 : ℝ)^3337 := by
    have hnat : (5941362107 : ℕ)^4361*10000000000000^3337 ≤ 5064075040149^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5941362107 10000000000 5064075040149 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1778931283/10000000000 : ℝ), (606774753/1250000000 : ℝ), (5941362107/10000000000 : ℝ)] ![(5236380323403/50000000000000 : ℝ), (7777297787/20000000000 : ℝ), (5064075040149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1778931283/10000000000 : ℝ)|^4361 ≤ (5236380323403/50000000000000 : ℝ)^3337
        have hw : |(-1778931283/10000000000 : ℝ)|=(1778931283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(606774753/1250000000 : ℝ)|^4361 ≤ (7777297787/20000000000 : ℝ)^3337
        have hw : |(606774753/1250000000 : ℝ)|=(606774753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5941362107/10000000000 : ℝ)|^4361 ≤ (5064075040149/10000000000000 : ℝ)^3337
        have hw : |(5941362107/10000000000 : ℝ)|=(5941362107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295571113/2500000000 : ℝ)*x 0 + (-1307425259/10000000000 : ℝ)*x 1 + (148534033/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295571113/2500000000 : ℝ)^4361 ≤ (2647271931671/6250000000000 : ℝ)^3337 := by
    have hnat : (1295571113 : ℕ)^4361*6250000000000^3337 ≤ 2647271931671^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295571113 2500000000 2647271931671 6250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307425259/10000000000 : ℝ)^4361 ≤ (7002907441883/100000000000000 : ℝ)^3337 := by
    have hnat : (1307425259 : ℕ)^4361*100000000000000^3337 ≤ 7002907441883^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307425259 10000000000 7002907441883 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148534033/250000000 : ℝ)^4361 ≤ (25320370817571/50000000000000 : ℝ)^3337 := by
    have hnat : (148534033 : ℕ)^4361*50000000000000^3337 ≤ 25320370817571^3337*250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148534033 250000000 25320370817571 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295571113/2500000000 : ℝ), (-1307425259/10000000000 : ℝ), (148534033/250000000 : ℝ)] ![(2647271931671/6250000000000 : ℝ), (7002907441883/100000000000000 : ℝ), (25320370817571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295571113/2500000000 : ℝ)|^4361 ≤ (2647271931671/6250000000000 : ℝ)^3337
        have hw : |(1295571113/2500000000 : ℝ)|=(1295571113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307425259/10000000000 : ℝ)|^4361 ≤ (7002907441883/100000000000000 : ℝ)^3337
        have hw : |(-1307425259/10000000000 : ℝ)|=(1307425259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148534033/250000000 : ℝ)|^4361 ≤ (25320370817571/50000000000000 : ℝ)^3337
        have hw : |(148534033/250000000 : ℝ)|=(148534033/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591140763/5000000000 : ℝ)*x 0 + (5941364131/10000000000 : ℝ)*x 1 + (-5229701/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591140763/5000000000 : ℝ)^4361 ≤ (8471263930607/20000000000000 : ℝ)^3337 := by
    have hnat : (2591140763 : ℕ)^4361*20000000000000^3337 ≤ 8471263930607^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591140763 5000000000 8471263930607 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5941364131/10000000000 : ℝ)^4361 ≤ (6330096618339/12500000000000 : ℝ)^3337 := by
    have hnat : (5941364131 : ℕ)^4361*12500000000000^3337 ≤ 6330096618339^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5941364131 10000000000 6330096618339 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229701/40000000 : ℝ)^4361 ≤ (1750726844721/25000000000000 : ℝ)^3337 := by
    have hnat : (5229701 : ℕ)^4361*25000000000000^3337 ≤ 1750726844721^3337*40000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229701 40000000 1750726844721 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591140763/5000000000 : ℝ), (5941364131/10000000000 : ℝ), (-5229701/40000000 : ℝ)] ![(8471263930607/20000000000000 : ℝ), (6330096618339/12500000000000 : ℝ), (1750726844721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591140763/5000000000 : ℝ)|^4361 ≤ (8471263930607/20000000000000 : ℝ)^3337
        have hw : |(2591140763/5000000000 : ℝ)|=(2591140763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5941364131/10000000000 : ℝ)|^4361 ≤ (6330096618339/12500000000000 : ℝ)^3337
        have hw : |(5941364131/10000000000 : ℝ)|=(5941364131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5229701/40000000 : ℝ)|^4361 ≤ (1750726844721/25000000000000 : ℝ)^3337
        have hw : |(-5229701/40000000 : ℝ)|=(5229701/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s0_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261183601/625000000 : ℝ)*x 0 + (5497167417/10000000000 : ℝ)*x 1 + (633874999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261183601/625000000 : ℝ)^4361 ≤ (15986568091123/50000000000000 : ℝ)^3337 := by
    have hnat : (261183601 : ℕ)^4361*50000000000000^3337 ≤ 15986568091123^3337*625000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261183601 625000000 15986568091123 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497167417/10000000000 : ℝ)^4361 ≤ (45750660576161/100000000000000 : ℝ)^3337 := by
    have hnat : (5497167417 : ℕ)^4361*100000000000000^3337 ≤ 45750660576161^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497167417 10000000000 45750660576161 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633874999/2000000000 : ℝ)^4361 ≤ (89104812879/400000000000 : ℝ)^3337 := by
    have hnat : (633874999 : ℕ)^4361*400000000000^3337 ≤ 89104812879^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633874999 2000000000 89104812879 400000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261183601/625000000 : ℝ), (5497167417/10000000000 : ℝ), (633874999/2000000000 : ℝ)] ![(15986568091123/50000000000000 : ℝ), (45750660576161/100000000000000 : ℝ), (89104812879/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261183601/625000000 : ℝ)|^4361 ≤ (15986568091123/50000000000000 : ℝ)^3337
        have hw : |(261183601/625000000 : ℝ)|=(261183601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497167417/10000000000 : ℝ)|^4361 ≤ (45750660576161/100000000000000 : ℝ)^3337
        have hw : |(5497167417/10000000000 : ℝ)|=(5497167417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633874999/2000000000 : ℝ)|^4361 ≤ (89104812879/400000000000 : ℝ)^3337
        have hw : |(633874999/2000000000 : ℝ)|=(633874999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (231/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26453/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (545/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^545 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^545*1^128 ≤ 0^128*1^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (545/128 : ℝ) ≤ (1010685560759566183/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^545 ≤ (1010685560759566183/50000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^545*50000000000000000000^128 ≤ 1010685560759566183^128*5^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1010685560759566183 50000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1010685560759566183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^545 := by
      have hnat : (1 : ℕ)^128*1^545 ≤ 1^545*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (51010685560759566183/50000000000000000000 : ℝ) ≤ (20094223169153/20000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (51010685560759566183/50000000000000000000 : ℝ)^128 ≤ (20094223169153/20000000000000 : ℝ)^545 := by
      have hnat : (51010685560759566183 : ℕ)^128*20000000000000^545 ≤ 20094223169153^545*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51010685560759566183 50000000000000000000 20094223169153 20000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20094223169153/20000000000000 : ℝ)) (X := (51010685560759566183/50000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (26010685560759566183/25000000000000000000 : ℝ) ≤ (10094223169153/10000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (26010685560759566183/25000000000000000000 : ℝ)^128 ≤ (10094223169153/10000000000000 : ℝ)^545 := by
      have hnat : (26010685560759566183 : ℕ)^128*10000000000000^545 ≤ 10094223169153^545*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26010685560759566183 25000000000000000000 10094223169153 10000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10094223169153/10000000000000 : ℝ)) (X := (26010685560759566183/25000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(94223169153/8000000000000 : ℝ)*(0 : ℝ))^(545/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(94223169153/8000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1010685560759566183/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(94223169153/8000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(545/128 : ℝ) := by
    rw [show (1 : ℝ)+(94223169153/8000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(20094223169153/20000000000000 : ℝ) by norm_num, show 1+(1010685560759566183/50000000000000000000 : ℝ)+(0 : ℝ)=(51010685560759566183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1010685560759566183/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(94223169153/8000000000000 : ℝ)*(2/5 : ℝ))^(545/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(94223169153/8000000000000 : ℝ)*(2/5 : ℝ)=(10094223169153/10000000000000 : ℝ) by norm_num, show 1+2*(1010685560759566183/50000000000000000000 : ℝ)=(26010685560759566183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(94223169153/8000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (94223169153/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(94223169153/8000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (94223169153/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(94223169153/8000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (94223169153/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-55461757/312500000 : ℝ)*X 0 0+(186619423/312500000 : ℝ)*X 0 1+(4824789413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1373804449/2500000000 : ℝ)*X 1 0+(-2423999043/10000000000 : ℝ)*X 1 1+(4824789657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099043593/2000000000 : ℝ)*X 2 0+(4824789563/10000000000 : ℝ)*X 2 1+(-1211999471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2085021939/5000000000 : ℝ)*X 0 0+(3104154639/10000000000 : ℝ)*X 0 1+(5560135507/10000000000 : ℝ)*X 0 2+(2085021939/5000000000 : ℝ)*X 1 0+(3104154639/10000000000 : ℝ)*X 1 1+(5560135507/10000000000 : ℝ)*X 1 2+(2085021939/5000000000 : ℝ)*X 2 0+(3104154639/10000000000 : ℝ)*X 2 1+(5560135507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1778931283/10000000000 : ℝ)*X 0 0+(606774753/1250000000 : ℝ)*X 0 1+(5941362107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1295571113/2500000000 : ℝ)*X 1 0+(-1307425259/10000000000 : ℝ)*X 1 1+(148534033/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591140763/5000000000 : ℝ)*X 2 0+(5941364131/10000000000 : ℝ)*X 2 1+(-5229701/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261183601/625000000 : ℝ)*X 0 0+(5497167417/10000000000 : ℝ)*X 0 1+(633874999/2000000000 : ℝ)*X 0 2+(261183601/625000000 : ℝ)*X 1 0+(5497167417/10000000000 : ℝ)*X 1 1+(633874999/2000000000 : ℝ)*X 1 2+(261183601/625000000 : ℝ)*X 2 0+(5497167417/10000000000 : ℝ)*X 2 1+(633874999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (193402907438234465763/40000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22972129/2000000000000 : ℝ)*(base19) + (29245129/2500000000000 : ℝ)*(base23) + (13501343/10000000000000 : ℝ)*(upper3) + (3084641/100000000000000 : ℝ)*(upper4) + (16493589/10000000000000 : ℝ)*(upper5) + (319749171822521/50000000000000 : ℝ)*(major0) + (319749171822521/50000000000000 : ℝ)*(major1) + (639498343645043/100000000000000 : ℝ)*(major2) + (21795475225713/2500000000000 : ℝ)*(sp0) + (871822165444569/100000000000000 : ℝ)*(sp1) + (871822144245859/100000000000000 : ℝ)*(sp2) + (407171234756147/100000000000000 : ℝ)*(sp3) + (4305022499/100000000000000 : ℝ)*(sp4) + (98865691/5000000000000 : ℝ)*(sp7) + (203586606034983/50000000000000 : ℝ)*(f.failure) + (43591165702551/5000000000000 : ℝ)*(f.sum) + (180137288639/160000000000000000000000000 : ℝ)*base66 + (4452555096621/800000000000000000000000000 : ℝ)*base68 + (1117779261913/400000000000000000000000000 : ℝ)*base69 + (1370997929421/800000000000000000000000000 : ℝ)*base72 + (1264144475359/160000000000000000000000000 : ℝ)*base74 + (1411411789913/400000000000000000000000000 : ℝ)*base75 + (2305933353687/400000000000000000000000000 : ℝ)*base78 + (1838837501287/400000000000000000000000000 : ℝ)*base80 + (981174355487/200000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16077997/5000000000000000000000 : ℝ)*base89 + (16077997/5000000000000000000000 : ℝ)*base91 + (33922003/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1868295394489492840347/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1952892749/100000000000000 : ℝ)*(base19) + (1888092313/100000000000000 : ℝ)*(base23) + (135958443/25000000000000 : ℝ)*(base39) + (57081757/100000000000000 : ℝ)*(upper3) + (408571687/100000000000000 : ℝ)*(upper5) + (674706194403633/100000000000000 : ℝ)*(major0) + (674706194403633/100000000000000 : ℝ)*(major1) + (674705650569861/100000000000000 : ℝ)*(major2) + (5939044843/100000000000000 : ℝ)*(sp1) + (4665019953/100000000000000 : ℝ)*(sp2) + (459910614385093/50000000000000 : ℝ)*(sp4) + (459906668416297/50000000000000 : ℝ)*(sp5) + (919815219491691/100000000000000 : ℝ)*(sp6) + (429590304820737/100000000000000 : ℝ)*(sp7) + (429590304820737/100000000000000 : ℝ)*(f.failure) + (459910886301979/50000000000000 : ℝ)*(f.sum) + (528224026309/400000000000000000000000000 : ℝ)*base66 + (5488935663333/800000000000000000000000000 : ℝ)*base67 + (5679493840751/800000000000000000000000000 : ℝ)*base70 + (3088008691333/800000000000000000000000000 : ℝ)*base71 + (29477978309/400000000000000000000000000 : ℝ)*base74 + (1648062663951/800000000000000000000000000 : ℝ)*base76 + (4674117450449/800000000000000000000000000 : ℝ)*base77 + (5739386821649/800000000000000000000000000 : ℝ)*base79 + (2524196802751/400000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3830517/10000000000000000000000 : ℝ)*base90 + (3830517/10000000000000000000000 : ℝ)*base92 + (3830517/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1401_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (231/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26453/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s1_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487778413/2500000000 : ℝ)*x 0 + (5616659417/10000000000 : ℝ)*x 1 + (5066950539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487778413/2500000000 : ℝ)^4361 ≤ (472668791027/4000000000000 : ℝ)^3337 := by
    have hnat : (487778413 : ℕ)^4361*4000000000000^3337 ≤ 472668791027^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487778413 2500000000 472668791027 4000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616659417/10000000000 : ℝ)^4361 ≤ (23527312815303/50000000000000 : ℝ)^3337 := by
    have hnat : (5616659417 : ℕ)^4361*50000000000000^3337 ≤ 23527312815303^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616659417 10000000000 23527312815303 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5066950539/10000000000 : ℝ)^4361 ≤ (41128654570971/100000000000000 : ℝ)^3337 := by
    have hnat : (5066950539 : ℕ)^4361*100000000000000^3337 ≤ 41128654570971^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066950539 10000000000 41128654570971 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487778413/2500000000 : ℝ), (5616659417/10000000000 : ℝ), (5066950539/10000000000 : ℝ)] ![(472668791027/4000000000000 : ℝ), (23527312815303/50000000000000 : ℝ), (41128654570971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487778413/2500000000 : ℝ)|^4361 ≤ (472668791027/4000000000000 : ℝ)^3337
        have hw : |(-487778413/2500000000 : ℝ)|=(487778413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616659417/10000000000 : ℝ)|^4361 ≤ (23527312815303/50000000000000 : ℝ)^3337
        have hw : |(5616659417/10000000000 : ℝ)|=(5616659417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5066950539/10000000000 : ℝ)|^4361 ≤ (41128654570971/100000000000000 : ℝ)^3337
        have hw : |(5066950539/10000000000 : ℝ)|=(5066950539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674955059/1250000000 : ℝ)*x 0 + (-224303117/1000000000 : ℝ)*x 1 + (316684471/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674955059/1250000000 : ℝ)^4361 ≤ (44692810266409/100000000000000 : ℝ)^3337 := by
    have hnat : (674955059 : ℕ)^4361*100000000000000^3337 ≤ 44692810266409^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674955059 1250000000 44692810266409 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224303117/1000000000 : ℝ)^4361 ≤ (27692430811/195312500000 : ℝ)^3337 := by
    have hnat : (224303117 : ℕ)^4361*195312500000^3337 ≤ 27692430811^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224303117 1000000000 27692430811 195312500000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316684471/625000000 : ℝ)^4361 ≤ (20564332573503/50000000000000 : ℝ)^3337 := by
    have hnat : (316684471 : ℕ)^4361*50000000000000^3337 ≤ 20564332573503^3337*625000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316684471 625000000 20564332573503 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674955059/1250000000 : ℝ), (-224303117/1000000000 : ℝ), (316684471/625000000 : ℝ)] ![(44692810266409/100000000000000 : ℝ), (27692430811/195312500000 : ℝ), (20564332573503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674955059/1250000000 : ℝ)|^4361 ≤ (44692810266409/100000000000000 : ℝ)^3337
        have hw : |(674955059/1250000000 : ℝ)|=(674955059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224303117/1000000000 : ℝ)|^4361 ≤ (27692430811/195312500000 : ℝ)^3337
        have hw : |(-224303117/1000000000 : ℝ)|=(224303117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316684471/625000000 : ℝ)|^4361 ≤ (20564332573503/50000000000000 : ℝ)^3337
        have hw : |(316684471/625000000 : ℝ)|=(316684471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399641203/10000000000 : ℝ)*x 0 + (2533475443/5000000000 : ℝ)*x 1 + (-2243031047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399641203/10000000000 : ℝ)^4361 ≤ (44692818173561/100000000000000 : ℝ)^3337 := by
    have hnat : (5399641203 : ℕ)^4361*100000000000000^3337 ≤ 44692818173561^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399641203 10000000000 44692818173561 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533475443/5000000000 : ℝ)^4361 ≤ (20564329125949/50000000000000 : ℝ)^3337 := by
    have hnat : (2533475443 : ℕ)^4361*50000000000000^3337 ≤ 20564329125949^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533475443 5000000000 20564329125949 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243031047/10000000000 : ℝ)^4361 ≤ (2835704711829/20000000000000 : ℝ)^3337 := by
    have hnat : (2243031047 : ℕ)^4361*20000000000000^3337 ≤ 2835704711829^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243031047 10000000000 2835704711829 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399641203/10000000000 : ℝ), (2533475443/5000000000 : ℝ), (-2243031047/10000000000 : ℝ)] ![(44692818173561/100000000000000 : ℝ), (20564329125949/50000000000000 : ℝ), (2835704711829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399641203/10000000000 : ℝ)|^4361 ≤ (44692818173561/100000000000000 : ℝ)^3337
        have hw : |(5399641203/10000000000 : ℝ)|=(5399641203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2533475443/5000000000 : ℝ)|^4361 ≤ (20564329125949/50000000000000 : ℝ)^3337
        have hw : |(2533475443/5000000000 : ℝ)|=(2533475443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243031047/10000000000 : ℝ)|^4361 ≤ (2835704711829/20000000000000 : ℝ)^3337
        have hw : |(-2243031047/10000000000 : ℝ)|=(2243031047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281713297/10000000000 : ℝ)*x 0 + (3729743481/10000000000 : ℝ)*x 1 + (2453378531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281713297/10000000000 : ℝ)^4361 ≤ (33004628775351/100000000000000 : ℝ)^3337 := by
    have hnat : (4281713297 : ℕ)^4361*100000000000000^3337 ≤ 33004628775351^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281713297 10000000000 33004628775351 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3729743481/10000000000 : ℝ)^4361 ≤ (13778861179531/50000000000000 : ℝ)^3337 := by
    have hnat : (3729743481 : ℕ)^4361*50000000000000^3337 ≤ 13778861179531^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729743481 10000000000 13778861179531 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2453378531/5000000000 : ℝ)^4361 ≤ (39437648850303/100000000000000 : ℝ)^3337 := by
    have hnat : (2453378531 : ℕ)^4361*100000000000000^3337 ≤ 39437648850303^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453378531 5000000000 39437648850303 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281713297/10000000000 : ℝ), (3729743481/10000000000 : ℝ), (2453378531/5000000000 : ℝ)] ![(33004628775351/100000000000000 : ℝ), (13778861179531/50000000000000 : ℝ), (39437648850303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281713297/10000000000 : ℝ)|^4361 ≤ (33004628775351/100000000000000 : ℝ)^3337
        have hw : |(4281713297/10000000000 : ℝ)|=(4281713297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3729743481/10000000000 : ℝ)|^4361 ≤ (13778861179531/50000000000000 : ℝ)^3337
        have hw : |(3729743481/10000000000 : ℝ)|=(3729743481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2453378531/5000000000 : ℝ)|^4361 ≤ (39437648850303/100000000000000 : ℝ)^3337
        have hw : |(2453378531/5000000000 : ℝ)|=(2453378531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975775899/5000000000 : ℝ)*x 0 + (634192463/1250000000 : ℝ)*x 1 + (5609955997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975775899/5000000000 : ℝ)^4361 ≤ (11820187767481/100000000000000 : ℝ)^3337 := by
    have hnat : (975775899 : ℕ)^4361*100000000000000^3337 ≤ 11820187767481^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975775899 5000000000 11820187767481 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634192463/1250000000 : ℝ)^4361 ≤ (41198565442909/100000000000000 : ℝ)^3337 := by
    have hnat : (634192463 : ℕ)^4361*100000000000000^3337 ≤ 41198565442909^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634192463 1250000000 41198565442909 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5609955997/10000000000 : ℝ)^4361 ≤ (9396249353227/20000000000000 : ℝ)^3337 := by
    have hnat : (5609955997 : ℕ)^4361*20000000000000^3337 ≤ 9396249353227^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609955997 10000000000 9396249353227 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975775899/5000000000 : ℝ), (634192463/1250000000 : ℝ), (5609955997/10000000000 : ℝ)] ![(11820187767481/100000000000000 : ℝ), (41198565442909/100000000000000 : ℝ), (9396249353227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975775899/5000000000 : ℝ)|^4361 ≤ (11820187767481/100000000000000 : ℝ)^3337
        have hw : |(-975775899/5000000000 : ℝ)|=(975775899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634192463/1250000000 : ℝ)|^4361 ≤ (41198565442909/100000000000000 : ℝ)^3337
        have hw : |(634192463/1250000000 : ℝ)|=(634192463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5609955997/10000000000 : ℝ)|^4361 ≤ (9396249353227/20000000000000 : ℝ)^3337
        have hw : |(5609955997/10000000000 : ℝ)|=(5609955997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657040033/1250000000 : ℝ)*x 0 + (-850013309/5000000000 : ℝ)*x 1 + (560995593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657040033/1250000000 : ℝ)^4361 ≤ (21574441461573/50000000000000 : ℝ)^3337 := by
    have hnat : (657040033 : ℕ)^4361*50000000000000^3337 ≤ 21574441461573^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657040033 1250000000 21574441461573 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850013309/5000000000 : ℝ)^4361 ≤ (2467467756703/25000000000000 : ℝ)^3337 := by
    have hnat : (850013309 : ℕ)^4361*25000000000000^3337 ≤ 2467467756703^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850013309 5000000000 2467467756703 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560995593/1000000000 : ℝ)^4361 ≤ (9396249206571/20000000000000 : ℝ)^3337 := by
    have hnat : (560995593 : ℕ)^4361*20000000000000^3337 ≤ 9396249206571^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560995593 1000000000 9396249206571 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657040033/1250000000 : ℝ), (-850013309/5000000000 : ℝ), (560995593/1000000000 : ℝ)] ![(21574441461573/50000000000000 : ℝ), (2467467756703/25000000000000 : ℝ), (9396249206571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657040033/1250000000 : ℝ)|^4361 ≤ (21574441461573/50000000000000 : ℝ)^3337
        have hw : |(657040033/1250000000 : ℝ)|=(657040033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-850013309/5000000000 : ℝ)|^4361 ≤ (2467467756703/25000000000000 : ℝ)^3337
        have hw : |(-850013309/5000000000 : ℝ)|=(850013309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560995593/1000000000 : ℝ)|^4361 ≤ (9396249206571/20000000000000 : ℝ)^3337
        have hw : |(560995593/1000000000 : ℝ)|=(560995593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256320801/10000000000 : ℝ)*x 0 + (560995637/1000000000 : ℝ)*x 1 + (-212503153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256320801/10000000000 : ℝ)^4361 ≤ (43148888684067/100000000000000 : ℝ)^3337 := by
    have hnat : (5256320801 : ℕ)^4361*100000000000000^3337 ≤ 43148888684067^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256320801 10000000000 43148888684067 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560995637/1000000000 : ℝ)^4361 ≤ (5872656356053/12500000000000 : ℝ)^3337 := by
    have hnat : (560995637 : ℕ)^4361*12500000000000^3337 ≤ 5872656356053^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560995637 1000000000 5872656356053 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212503153/1250000000 : ℝ)^4361 ≤ (9869860450157/100000000000000 : ℝ)^3337 := by
    have hnat : (212503153 : ℕ)^4361*100000000000000^3337 ≤ 9869860450157^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212503153 1250000000 9869860450157 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256320801/10000000000 : ℝ), (560995637/1000000000 : ℝ), (-212503153/1250000000 : ℝ)] ![(43148888684067/100000000000000 : ℝ), (5872656356053/12500000000000 : ℝ), (9869860450157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256320801/10000000000 : ℝ)|^4361 ≤ (43148888684067/100000000000000 : ℝ)^3337
        have hw : |(5256320801/10000000000 : ℝ)|=(5256320801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560995637/1000000000 : ℝ)|^4361 ≤ (5872656356053/12500000000000 : ℝ)^3337
        have hw : |(560995637/1000000000 : ℝ)|=(560995637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212503153/1250000000 : ℝ)|^4361 ≤ (9869860450157/100000000000000 : ℝ)^3337
        have hw : |(-212503153/1250000000 : ℝ)|=(212503153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s1_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141326581/5000000000 : ℝ)*x 0 + (2446323967/5000000000 : ℝ)*x 1 + (3744095699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141326581/5000000000 : ℝ)^4361 ≤ (4126762121451/12500000000000 : ℝ)^3337 := by
    have hnat : (2141326581 : ℕ)^4361*12500000000000^3337 ≤ 4126762121451^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141326581 5000000000 4126762121451 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2446323967/5000000000 : ℝ)^4361 ≤ (1227797339183/3125000000000 : ℝ)^3337 := by
    have hnat : (2446323967 : ℕ)^4361*3125000000000^3337 ≤ 1227797339183^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446323967 5000000000 1227797339183 3125000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3744095699/10000000000 : ℝ)^4361 ≤ (27696388161101/100000000000000 : ℝ)^3337 := by
    have hnat : (3744095699 : ℕ)^4361*100000000000000^3337 ≤ 27696388161101^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744095699 10000000000 27696388161101 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141326581/5000000000 : ℝ), (2446323967/5000000000 : ℝ), (3744095699/10000000000 : ℝ)] ![(4126762121451/12500000000000 : ℝ), (1227797339183/3125000000000 : ℝ), (27696388161101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141326581/5000000000 : ℝ)|^4361 ≤ (4126762121451/12500000000000 : ℝ)^3337
        have hw : |(2141326581/5000000000 : ℝ)|=(2141326581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2446323967/5000000000 : ℝ)|^4361 ≤ (1227797339183/3125000000000 : ℝ)^3337
        have hw : |(2446323967/5000000000 : ℝ)|=(2446323967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3744095699/10000000000 : ℝ)|^4361 ≤ (27696388161101/100000000000000 : ℝ)^3337
        have hw : |(3744095699/10000000000 : ℝ)|=(3744095699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (231/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (927/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4759/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (231/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (231/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (231/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (231/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (231/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (231/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (231/12500 : ℝ) ^ (545/128 : ℝ) ≤ (32563569059/781250000000000000 : ℝ) := by
    have hpowers : (231/12500 : ℝ)^545 ≤ (32563569059/781250000000000000 : ℝ)^128 := by
      have hnat : (231 : ℕ)^545*781250000000000000^128 ≤ 32563569059^128*12500^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        231 12500 32563569059 781250000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (231/12500 : ℝ)) (X := (32563569059/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (26453/100000 : ℝ) ^ (545/128 : ℝ) ≤ (43442674986194679/12500000000000000000 : ℝ) := by
    have hpowers : (26453/100000 : ℝ)^545 ≤ (43442674986194679/12500000000000000000 : ℝ)^128 := by
      have hnat : (26453 : ℕ)^545*12500000000000000000^128 ≤ 43442674986194679^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26453 100000 43442674986194679 12500000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26453/100000 : ℝ)) (X := (43442674986194679/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (390625032563569059/390625000000000000 : ℝ) ≤ (5000000097893853/5000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (390625032563569059/390625000000000000 : ℝ)^128 ≤ (5000000097893853/5000000000000000 : ℝ)^545 := by
      have hnat : (390625032563569059 : ℕ)^128*5000000000000000^545 ≤ 5000000097893853^545*390625000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390625032563569059 390625000000000000 5000000097893853 5000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000097893853/5000000000000000 : ℝ)) (X := (390625032563569059/390625000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12543443196003299623/12500000000000000000 : ℝ) ≤ (625509481708309/625000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12543443196003299623/12500000000000000000 : ℝ)^128 ≤ (625509481708309/625000000000000 : ℝ)^545 := by
      have hnat : (12543443196003299623 : ℕ)^128*625000000000000^545 ≤ 625509481708309^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12543443196003299623 12500000000000000000 625509481708309 625000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625509481708309/625000000000000 : ℝ)) (X := (12543443196003299623/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6293442674986194679/6250000000000000000 : ℝ) ≤ (5008151609439091/5000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (6293442674986194679/6250000000000000000 : ℝ)^128 ≤ (5008151609439091/5000000000000000 : ℝ)^545 := by
      have hnat : (6293442674986194679 : ℕ)^128*5000000000000000^545 ≤ 5008151609439091^545*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6293442674986194679 6250000000000000000 5008151609439091 5000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008151609439091/5000000000000000 : ℝ)) (X := (6293442674986194679/6250000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(32563569059/781250000000000000 : ℝ) ≤ ((17572848345048950463/17575000000000000000 : ℝ)+2*(4075755772619/1230250000000000 : ℝ)*(231/12500 : ℝ))^(545/128 : ℝ) := by
    rw [show (17572848345048950463/17575000000000000000 : ℝ)+2*(4075755772619/1230250000000000 : ℝ)*(231/12500 : ℝ)=(5000000097893853/5000000000000000 : ℝ) by norm_num, show 1+2*(32563569059/781250000000000000 : ℝ)=(390625032563569059/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43442674986194679/12500000000000000000 : ℝ)+(32563569059/781250000000000000 : ℝ) ≤ ((17572848345048950463/17575000000000000000 : ℝ)+(4075755772619/1230250000000000 : ℝ)*((26453/100000 : ℝ)+(231/12500 : ℝ)))^(545/128 : ℝ) := by
    rw [show (17572848345048950463/17575000000000000000 : ℝ)+(4075755772619/1230250000000000 : ℝ)*((26453/100000 : ℝ)+(231/12500 : ℝ))=(625509481708309/625000000000000 : ℝ) by norm_num, show 1+(43442674986194679/12500000000000000000 : ℝ)+(32563569059/781250000000000000 : ℝ)=(12543443196003299623/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43442674986194679/12500000000000000000 : ℝ) ≤ ((17572848345048950463/17575000000000000000 : ℝ)+2*(4075755772619/1230250000000000 : ℝ)*(26453/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (17572848345048950463/17575000000000000000 : ℝ)+2*(4075755772619/1230250000000000 : ℝ)*(26453/100000 : ℝ)=(5008151609439091/5000000000000000 : ℝ) by norm_num, show 1+2*(43442674986194679/12500000000000000000 : ℝ)=(6293442674986194679/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17572848345048950463/17575000000000000000 : ℝ)*(X 1 0+X 2 0)+(4075755772619/1230250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (231/12500 : ℝ)) (hi := (26453/100000 : ℝ)) (c := (17572848345048950463/17575000000000000000 : ℝ)) (alpha := (4075755772619/1230250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17572848345048950463/17575000000000000000 : ℝ)*(X 0 1+X 2 1)+(4075755772619/1230250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (231/12500 : ℝ)) (hi := (26453/100000 : ℝ)) (c := (17572848345048950463/17575000000000000000 : ℝ)) (alpha := (4075755772619/1230250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17572848345048950463/17575000000000000000 : ℝ)*(X 0 2+X 1 2)+(4075755772619/1230250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (231/12500 : ℝ)) (hi := (26453/100000 : ℝ)) (c := (17572848345048950463/17575000000000000000 : ℝ)) (alpha := (4075755772619/1230250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487778413/2500000000 : ℝ)*X 0 0+(5616659417/10000000000 : ℝ)*X 0 1+(5066950539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((674955059/1250000000 : ℝ)*X 1 0+(-224303117/1000000000 : ℝ)*X 1 1+(316684471/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5399641203/10000000000 : ℝ)*X 2 0+(2533475443/5000000000 : ℝ)*X 2 1+(-2243031047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4281713297/10000000000 : ℝ)*X 0 0+(3729743481/10000000000 : ℝ)*X 0 1+(2453378531/5000000000 : ℝ)*X 0 2+(4281713297/10000000000 : ℝ)*X 1 0+(3729743481/10000000000 : ℝ)*X 1 1+(2453378531/5000000000 : ℝ)*X 1 2+(4281713297/10000000000 : ℝ)*X 2 0+(3729743481/10000000000 : ℝ)*X 2 1+(2453378531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975775899/5000000000 : ℝ)*X 0 0+(634192463/1250000000 : ℝ)*X 0 1+(5609955997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657040033/1250000000 : ℝ)*X 1 0+(-850013309/5000000000 : ℝ)*X 1 1+(560995593/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256320801/10000000000 : ℝ)*X 2 0+(560995637/1000000000 : ℝ)*X 2 1+(-212503153/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141326581/5000000000 : ℝ)*X 0 0+(2446323967/5000000000 : ℝ)*X 0 1+(3744095699/10000000000 : ℝ)*X 0 2+(2141326581/5000000000 : ℝ)*X 1 0+(2446323967/5000000000 : ℝ)*X 1 1+(3744095699/10000000000 : ℝ)*X 1 2+(2141326581/5000000000 : ℝ)*X 2 0+(2446323967/5000000000 : ℝ)*X 2 1+(3744095699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526505863655537178541971/61512500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9108249/100000000000000 : ℝ)*(base1) + (811469867/50000000000000 : ℝ)*(base19) + (934609017/50000000000000 : ℝ)*(base23) + (139537719/100000000000000 : ℝ)*(upper3) + (31185287/12500000000000 : ℝ)*(upper5) + (667198404133913/50000000000000 : ℝ)*(major0) + (667198404133913/50000000000000 : ℝ)*(major1) + (667198404133913/50000000000000 : ℝ)*(major2) + (1819157829859293/100000000000000 : ℝ)*(sp0) + (36383432543469/2000000000000 : ℝ)*(sp1) + (1819171380895149/100000000000000 : ℝ)*(sp2) + (849614034693867/100000000000000 : ℝ)*(sp3) + (15429362139/100000000000000 : ℝ)*(sp4) + (6037309307/100000000000000 : ℝ)*(sp7) + (849620081111423/100000000000000 : ℝ)*(f.failure) + (1819173250113183/100000000000000 : ℝ)*(f.sum) + (139763444019287/123025000000000000000000000000 : ℝ)*base66 + (1528675741150337967/6151250000000000000000000000000000 : ℝ)*base68 + (27740284159469087967/6151250000000000000000000000000000 : ℝ)*base70 + (2176438467160912033/6151250000000000000000000000000000 : ℝ)*base71 + (97459082089037/123025000000000000000000000000 : ℝ)*base74 + (60265711718831587967/6151250000000000000000000000000000 : ℝ)*base76 + (14605925813302162033/6151250000000000000000000000000000 : ℝ)*base77 + (15237337484078412033/6151250000000000000000000000000000 : ℝ)*base79 + (153018228214503/30756250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (59107957/10000000000000000000000 : ℝ)*base89 + (59107957/10000000000000000000000 : ℝ)*base91 + (59107957/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10330965212212788862975437339/6151250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88136543/50000000000000 : ℝ)*(base1) + (136820963/20000000000000 : ℝ)*(base19) + (122879583/12500000000000 : ℝ)*(base23) + (8390839/25000000000000 : ℝ)*(upper3) + (39624711/25000000000000 : ℝ)*(upper5) + (1367443625650103/100000000000000 : ℝ)*(major0) + (1367443625650103/100000000000000 : ℝ)*(major1) + (170930453206263/12500000000000 : ℝ)*(major2) + (2861540983/100000000000000 : ℝ)*(sp1) + (6839984759/100000000000000 : ℝ)*(sp2) + (932113071639863/50000000000000 : ℝ)*(sp4) + (932111210680421/50000000000000 : ℝ)*(sp5) + (932109071992609/50000000000000 : ℝ)*(sp6) + (43533052601873/5000000000000 : ℝ)*(sp7) + (870661228310547/100000000000000 : ℝ)*(f.failure) + (23302824587583/1250000000000 : ℝ)*(f.sum) + (44938875446833/123025000000000000000000000000 : ℝ)*base65 + (4460458640702533823/12302500000000000000000000000000000 : ℝ)*base67 + (23433738705729785883/1537812500000000000000000000000000 : ℝ)*base69 + (43907612433602533823/12302500000000000000000000000000000 : ℝ)*base71 + (343337128649217/123025000000000000000000000000 : ℝ)*base74 + (18413894075715410883/1537812500000000000000000000000000 : ℝ)*base75 + (10970031708963133823/12302500000000000000000000000000000 : ℝ)*base77 + (34173986615634366177/12302500000000000000000000000000000 : ℝ)*base80 + (99086932228639/123025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (61048273/10000000000000000000000 : ℝ)*base89 + (61048273/10000000000000000000000 : ℝ)*base91 + (38951727/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1401_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (231/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (927/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4759/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s2_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-496597857/2500000000 : ℝ)*x 0 + (683081413/1250000000 : ℝ)*x 1 + (5196285969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496597857/2500000000 : ℝ)^4361 ≤ (302417761837/2500000000000 : ℝ)^3337 := by
    have hnat : (496597857 : ℕ)^4361*2500000000000^3337 ≤ 302417761837^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496597857 2500000000 302417761837 2500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683081413/1250000000 : ℝ)^4361 ≤ (567466514943/1250000000000 : ℝ)^3337 := by
    have hnat : (683081413 : ℕ)^4361*1250000000000^3337 ≤ 567466514943^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683081413 1250000000 567466514943 1250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196285969/10000000000 : ℝ)^4361 ≤ (5313246040159/12500000000000 : ℝ)^3337 := by
    have hnat : (5196285969 : ℕ)^4361*12500000000000^3337 ≤ 5313246040159^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196285969 10000000000 5313246040159 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496597857/2500000000 : ℝ), (683081413/1250000000 : ℝ), (5196285969/10000000000 : ℝ)] ![(302417761837/2500000000000 : ℝ), (567466514943/1250000000000 : ℝ), (5313246040159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496597857/2500000000 : ℝ)|^4361 ≤ (302417761837/2500000000000 : ℝ)^3337
        have hw : |(-496597857/2500000000 : ℝ)|=(496597857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683081413/1250000000 : ℝ)|^4361 ≤ (567466514943/1250000000000 : ℝ)^3337
        have hw : |(683081413/1250000000 : ℝ)|=(683081413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196285969/10000000000 : ℝ)|^4361 ≤ (5313246040159/12500000000000 : ℝ)^3337
        have hw : |(5196285969/10000000000 : ℝ)|=(5196285969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67024307/125000000 : ℝ)*x 0 + (-2124640843/10000000000 : ℝ)*x 1 + (1039257191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67024307/125000000 : ℝ)^4361 ≤ (4428549492751/10000000000000 : ℝ)^3337 := by
    have hnat : (67024307 : ℕ)^4361*10000000000000^3337 ≤ 4428549492751^3337*125000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67024307 125000000 4428549492751 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124640843/10000000000 : ℝ)^4361 ≤ (13208536885469/100000000000000 : ℝ)^3337 := by
    have hnat : (2124640843 : ℕ)^4361*100000000000000^3337 ≤ 13208536885469^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124640843 10000000000 13208536885469 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039257191/2000000000 : ℝ)^4361 ≤ (42505968171609/100000000000000 : ℝ)^3337 := by
    have hnat : (1039257191 : ℕ)^4361*100000000000000^3337 ≤ 42505968171609^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039257191 2000000000 42505968171609 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67024307/125000000 : ℝ), (-2124640843/10000000000 : ℝ), (1039257191/2000000000 : ℝ)] ![(4428549492751/10000000000000 : ℝ), (13208536885469/100000000000000 : ℝ), (42505968171609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67024307/125000000 : ℝ)|^4361 ≤ (4428549492751/10000000000000 : ℝ)^3337
        have hw : |(67024307/125000000 : ℝ)|=(67024307/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124640843/10000000000 : ℝ)|^4361 ≤ (13208536885469/100000000000000 : ℝ)^3337
        have hw : |(-2124640843/10000000000 : ℝ)|=(2124640843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039257191/2000000000 : ℝ)|^4361 ≤ (42505968171609/100000000000000 : ℝ)^3337
        have hw : |(1039257191/2000000000 : ℝ)|=(1039257191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680972183/5000000000 : ℝ)*x 0 + (2598143087/5000000000 : ℝ)*x 1 + (-2124640813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680972183/5000000000 : ℝ)^4361 ≤ (22142746416769/50000000000000 : ℝ)^3337 := by
    have hnat : (2680972183 : ℕ)^4361*50000000000000^3337 ≤ 22142746416769^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680972183 5000000000 22142746416769 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598143087/5000000000 : ℝ)^4361 ≤ (332077894631/781250000000 : ℝ)^3337 := by
    have hnat : (2598143087 : ℕ)^4361*781250000000^3337 ≤ 332077894631^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598143087 5000000000 332077894631 781250000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124640813/10000000000 : ℝ)^4361 ≤ (13208536641733/100000000000000 : ℝ)^3337 := by
    have hnat : (2124640813 : ℕ)^4361*100000000000000^3337 ≤ 13208536641733^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124640813 10000000000 13208536641733 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680972183/5000000000 : ℝ), (2598143087/5000000000 : ℝ), (-2124640813/10000000000 : ℝ)] ![(22142746416769/50000000000000 : ℝ), (332077894631/781250000000 : ℝ), (13208536641733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680972183/5000000000 : ℝ)|^4361 ≤ (22142746416769/50000000000000 : ℝ)^3337
        have hw : |(2680972183/5000000000 : ℝ)|=(2680972183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598143087/5000000000 : ℝ)|^4361 ≤ (332077894631/781250000000 : ℝ)^3337
        have hw : |(2598143087/5000000000 : ℝ)|=(2598143087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124640813/10000000000 : ℝ)|^4361 ≤ (13208536641733/100000000000000 : ℝ)^3337
        have hw : |(-2124640813/10000000000 : ℝ)|=(2124640813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306542349/10000000000 : ℝ)*x 0 + (1006985659/2500000000 : ℝ)*x 1 + (2301278107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306542349/10000000000 : ℝ)^4361 ≤ (33254970362957/100000000000000 : ℝ)^3337 := by
    have hnat : (4306542349 : ℕ)^4361*100000000000000^3337 ≤ 33254970362957^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306542349 10000000000 33254970362957 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006985659/2500000000 : ℝ)^4361 ≤ (380897547373/1250000000000 : ℝ)^3337 := by
    have hnat : (1006985659 : ℕ)^4361*1250000000000^3337 ≤ 380897547373^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006985659 2500000000 380897547373 1250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2301278107/5000000000 : ℝ)^4361 ≤ (36273225830217/100000000000000 : ℝ)^3337 := by
    have hnat : (2301278107 : ℕ)^4361*100000000000000^3337 ≤ 36273225830217^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301278107 5000000000 36273225830217 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306542349/10000000000 : ℝ), (1006985659/2500000000 : ℝ), (2301278107/5000000000 : ℝ)] ![(33254970362957/100000000000000 : ℝ), (380897547373/1250000000000 : ℝ), (36273225830217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306542349/10000000000 : ℝ)|^4361 ≤ (33254970362957/100000000000000 : ℝ)^3337
        have hw : |(4306542349/10000000000 : ℝ)|=(4306542349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006985659/2500000000 : ℝ)|^4361 ≤ (380897547373/1250000000000 : ℝ)^3337
        have hw : |(1006985659/2500000000 : ℝ)|=(1006985659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2301278107/5000000000 : ℝ)|^4361 ≤ (36273225830217/100000000000000 : ℝ)^3337
        have hw : |(2301278107/5000000000 : ℝ)|=(2301278107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-397288441/2000000000 : ℝ)*x 0 + (1299466487/2500000000 : ℝ)*x 1 + (1092611637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397288441/2000000000 : ℝ)^4361 ≤ (2419422916971/20000000000000 : ℝ)^3337 := by
    have hnat : (397288441 : ℕ)^4361*20000000000000^3337 ≤ 2419422916971^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397288441 2000000000 2419422916971 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299466487/2500000000 : ℝ)^4361 ≤ (21261429718239/50000000000000 : ℝ)^3337 := by
    have hnat : (1299466487 : ℕ)^4361*50000000000000^3337 ≤ 21261429718239^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299466487 2500000000 21261429718239 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092611637/2000000000 : ℝ)^4361 ≤ (45380025961487/100000000000000 : ℝ)^3337 := by
    have hnat : (1092611637 : ℕ)^4361*100000000000000^3337 ≤ 45380025961487^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092611637 2000000000 45380025961487 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397288441/2000000000 : ℝ), (1299466487/2500000000 : ℝ), (1092611637/2000000000 : ℝ)] ![(2419422916971/20000000000000 : ℝ), (21261429718239/50000000000000 : ℝ), (45380025961487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397288441/2000000000 : ℝ)|^4361 ≤ (2419422916971/20000000000000 : ℝ)^3337
        have hw : |(-397288441/2000000000 : ℝ)|=(397288441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299466487/2500000000 : ℝ)|^4361 ≤ (21261429718239/50000000000000 : ℝ)^3337
        have hw : |(1299466487/2500000000 : ℝ)|=(1299466487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092611637/2000000000 : ℝ)|^4361 ≤ (45380025961487/100000000000000 : ℝ)^3337
        have hw : |(1092611637/2000000000 : ℝ)|=(1092611637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10336619/19531250 : ℝ)*x 0 + (-92893461/500000000 : ℝ)*x 1 + (546305789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10336619/19531250 : ℝ)^4361 ≤ (8707160650883/20000000000000 : ℝ)^3337 := by
    have hnat : (10336619 : ℕ)^4361*20000000000000^3337 ≤ 8707160650883^3337*19531250^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10336619 19531250 8707160650883 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92893461/500000000 : ℝ)^4361 ≤ (173190218281/1562500000000 : ℝ)^3337 := by
    have hnat : (92893461 : ℕ)^4361*1562500000000^3337 ≤ 173190218281^3337*500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92893461 500000000 173190218281 1562500000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546305789/1000000000 : ℝ)^4361 ≤ (45380022759049/100000000000000 : ℝ)^3337 := by
    have hnat : (546305789 : ℕ)^4361*100000000000000^3337 ≤ 45380022759049^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546305789 1000000000 45380022759049 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10336619/19531250 : ℝ), (-92893461/500000000 : ℝ), (546305789/1000000000 : ℝ)] ![(8707160650883/20000000000000 : ℝ), (173190218281/1562500000000 : ℝ), (45380022759049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10336619/19531250 : ℝ)|^4361 ≤ (8707160650883/20000000000000 : ℝ)^3337
        have hw : |(10336619/19531250 : ℝ)|=(10336619/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92893461/500000000 : ℝ)|^4361 ≤ (173190218281/1562500000000 : ℝ)^3337
        have hw : |(-92893461/500000000 : ℝ)|=(92893461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546305789/1000000000 : ℝ)|^4361 ≤ (45380022759049/100000000000000 : ℝ)^3337
        have hw : |(546305789/1000000000 : ℝ)|=(546305789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292350341/10000000000 : ℝ)*x 0 + (546305787/1000000000 : ℝ)*x 1 + (-18578673/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292350341/10000000000 : ℝ)^4361 ≤ (43535818444847/100000000000000 : ℝ)^3337 := by
    have hnat : (5292350341 : ℕ)^4361*100000000000000^3337 ≤ 43535818444847^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292350341 10000000000 43535818444847 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546305787/1000000000 : ℝ)^4361 ≤ (22690011270967/50000000000000 : ℝ)^3337 := by
    have hnat : (546305787 : ℕ)^4361*50000000000000^3337 ≤ 22690011270967^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546305787 1000000000 22690011270967 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18578673/100000000 : ℝ)^4361 ≤ (1385519875009/12500000000000 : ℝ)^3337 := by
    have hnat : (18578673 : ℕ)^4361*12500000000000^3337 ≤ 1385519875009^3337*100000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18578673 100000000 1385519875009 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292350341/10000000000 : ℝ), (546305787/1000000000 : ℝ), (-18578673/100000000 : ℝ)] ![(43535818444847/100000000000000 : ℝ), (22690011270967/50000000000000 : ℝ), (1385519875009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292350341/10000000000 : ℝ)|^4361 ≤ (43535818444847/100000000000000 : ℝ)^3337
        have hw : |(5292350341/10000000000 : ℝ)|=(5292350341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546305787/1000000000 : ℝ)|^4361 ≤ (22690011270967/50000000000000 : ℝ)^3337
        have hw : |(546305787/1000000000 : ℝ)|=(546305787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18578673/100000000 : ℝ)|^4361 ≤ (1385519875009/12500000000000 : ℝ)^3337
        have hw : |(-18578673/100000000 : ℝ)|=(18578673/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s2_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153326179/5000000000 : ℝ)*x 0 + (459917373/1000000000 : ℝ)*x 1 + (2015676639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153326179/5000000000 : ℝ)^4361 ≤ (415701006603/1250000000000 : ℝ)^3337 := by
    have hnat : (2153326179 : ℕ)^4361*1250000000000^3337 ≤ 415701006603^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153326179 5000000000 415701006603 1250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459917373/1000000000 : ℝ)^4361 ≤ (9059597949933/25000000000000 : ℝ)^3337 := by
    have hnat : (459917373 : ℕ)^4361*25000000000000^3337 ≤ 9059597949933^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459917373 1000000000 9059597949933 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015676639/5000000000 : ℝ)^4361 ≤ (30505527652329/100000000000000 : ℝ)^3337 := by
    have hnat : (2015676639 : ℕ)^4361*100000000000000^3337 ≤ 30505527652329^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015676639 5000000000 30505527652329 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153326179/5000000000 : ℝ), (459917373/1000000000 : ℝ), (2015676639/5000000000 : ℝ)] ![(415701006603/1250000000000 : ℝ), (9059597949933/25000000000000 : ℝ), (30505527652329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153326179/5000000000 : ℝ)|^4361 ≤ (415701006603/1250000000000 : ℝ)^3337
        have hw : |(2153326179/5000000000 : ℝ)|=(2153326179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(459917373/1000000000 : ℝ)|^4361 ≤ (9059597949933/25000000000000 : ℝ)^3337
        have hw : |(459917373/1000000000 : ℝ)|=(459917373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015676639/5000000000 : ℝ)|^4361 ≤ (30505527652329/100000000000000 : ℝ)^3337
        have hw : |(2015676639/5000000000 : ℝ)|=(2015676639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4759/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (927/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10213/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15889/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4759/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (927/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4759/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (927/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4759/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (927/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4759/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (927/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4759/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (927/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4759/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (927/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (927/12500 : ℝ) ^ (545/128 : ℝ) ≤ (1546658795933833/100000000000000000000 : ℝ) := by
    have hpowers : (927/12500 : ℝ)^545 ≤ (1546658795933833/100000000000000000000 : ℝ)^128 := by
      have hnat : (927 : ℕ)^545*100000000000000000000^128 ≤ 1546658795933833^128*12500^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        927 12500 1546658795933833 100000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (927/12500 : ℝ)) (X := (1546658795933833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4759/25000 : ℝ) ^ (545/128 : ℝ) ≤ (21404663381765613/25000000000000000000 : ℝ) := by
    have hpowers : (4759/25000 : ℝ)^545 ≤ (21404663381765613/25000000000000000000 : ℝ)^128 := by
      have hnat : (4759 : ℕ)^545*25000000000000000000^128 ≤ 21404663381765613^128*25000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4759 25000 21404663381765613 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4759/25000 : ℝ)) (X := (21404663381765613/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001546658795933833/50000000000000000000 : ℝ) ≤ (2000014529907017/2000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (50001546658795933833/50000000000000000000 : ℝ)^128 ≤ (2000014529907017/2000000000000000 : ℝ)^545 := by
      have hnat : (50001546658795933833 : ℕ)^128*2000000000000000^545 ≤ 2000014529907017^545*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001546658795933833 50000000000000000000 2000014529907017 2000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014529907017/2000000000000000 : ℝ)) (X := (50001546658795933833/50000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20017433062464599257/20000000000000000000 : ℝ) ≤ (10002046502997497/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (20017433062464599257/20000000000000000000 : ℝ)^128 ≤ (10002046502997497/10000000000000000 : ℝ)^545 := by
      have hnat : (20017433062464599257 : ℕ)^128*10000000000000000^545 ≤ 10002046502997497^545*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20017433062464599257 20000000000000000000 10002046502997497 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002046502997497/10000000000000000 : ℝ)) (X := (20017433062464599257/20000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12521404663381765613/12500000000000000000 : ℝ) ≤ (10004020356459909/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12521404663381765613/12500000000000000000 : ℝ)^128 ≤ (10004020356459909/10000000000000000 : ℝ)^545 := by
      have hnat : (12521404663381765613 : ℕ)^128*10000000000000000^545 ≤ 10004020356459909^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12521404663381765613 12500000000000000000 10004020356459909 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004020356459909/10000000000000000 : ℝ)) (X := (12521404663381765613/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1546658795933833/100000000000000000000 : ℝ) ≤ ((29042891998260798229/29050000000000000000 : ℝ)+2*(493463365603/290500000000000 : ℝ)*(927/12500 : ℝ))^(545/128 : ℝ) := by
    rw [show (29042891998260798229/29050000000000000000 : ℝ)+2*(493463365603/290500000000000 : ℝ)*(927/12500 : ℝ)=(2000014529907017/2000000000000000 : ℝ) by norm_num, show 1+2*(1546658795933833/100000000000000000000 : ℝ)=(50001546658795933833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21404663381765613/25000000000000000000 : ℝ)+(1546658795933833/100000000000000000000 : ℝ) ≤ ((29042891998260798229/29050000000000000000 : ℝ)+(493463365603/290500000000000 : ℝ)*((4759/25000 : ℝ)+(927/12500 : ℝ)))^(545/128 : ℝ) := by
    rw [show (29042891998260798229/29050000000000000000 : ℝ)+(493463365603/290500000000000 : ℝ)*((4759/25000 : ℝ)+(927/12500 : ℝ))=(10002046502997497/10000000000000000 : ℝ) by norm_num, show 1+(21404663381765613/25000000000000000000 : ℝ)+(1546658795933833/100000000000000000000 : ℝ)=(20017433062464599257/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21404663381765613/25000000000000000000 : ℝ) ≤ ((29042891998260798229/29050000000000000000 : ℝ)+2*(493463365603/290500000000000 : ℝ)*(4759/25000 : ℝ))^(545/128 : ℝ) := by
    rw [show (29042891998260798229/29050000000000000000 : ℝ)+2*(493463365603/290500000000000 : ℝ)*(4759/25000 : ℝ)=(10004020356459909/10000000000000000 : ℝ) by norm_num, show 1+2*(21404663381765613/25000000000000000000 : ℝ)=(12521404663381765613/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29042891998260798229/29050000000000000000 : ℝ)*(X 1 0+X 2 0)+(493463365603/290500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (927/12500 : ℝ)) (hi := (4759/25000 : ℝ)) (c := (29042891998260798229/29050000000000000000 : ℝ)) (alpha := (493463365603/290500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29042891998260798229/29050000000000000000 : ℝ)*(X 0 1+X 2 1)+(493463365603/290500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (927/12500 : ℝ)) (hi := (4759/25000 : ℝ)) (c := (29042891998260798229/29050000000000000000 : ℝ)) (alpha := (493463365603/290500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29042891998260798229/29050000000000000000 : ℝ)*(X 0 2+X 1 2)+(493463365603/290500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (927/12500 : ℝ)) (hi := (4759/25000 : ℝ)) (c := (29042891998260798229/29050000000000000000 : ℝ)) (alpha := (493463365603/290500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-496597857/2500000000 : ℝ)*X 0 0+(683081413/1250000000 : ℝ)*X 0 1+(5196285969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((67024307/125000000 : ℝ)*X 1 0+(-2124640843/10000000000 : ℝ)*X 1 1+(1039257191/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680972183/5000000000 : ℝ)*X 2 0+(2598143087/5000000000 : ℝ)*X 2 1+(-2124640813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306542349/10000000000 : ℝ)*X 0 0+(1006985659/2500000000 : ℝ)*X 0 1+(2301278107/5000000000 : ℝ)*X 0 2+(4306542349/10000000000 : ℝ)*X 1 0+(1006985659/2500000000 : ℝ)*X 1 1+(2301278107/5000000000 : ℝ)*X 1 2+(4306542349/10000000000 : ℝ)*X 2 0+(1006985659/2500000000 : ℝ)*X 2 1+(2301278107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-397288441/2000000000 : ℝ)*X 0 0+(1299466487/2500000000 : ℝ)*X 0 1+(1092611637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10336619/19531250 : ℝ)*X 1 0+(-92893461/500000000 : ℝ)*X 1 1+(546305789/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292350341/10000000000 : ℝ)*X 2 0+(546305787/1000000000 : ℝ)*X 2 1+(-18578673/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153326179/5000000000 : ℝ)*X 0 0+(459917373/1000000000 : ℝ)*X 0 1+(2015676639/5000000000 : ℝ)*X 0 2+(2153326179/5000000000 : ℝ)*X 1 0+(459917373/1000000000 : ℝ)*X 1 1+(2015676639/5000000000 : ℝ)*X 1 2+(2153326179/5000000000 : ℝ)*X 2 0+(459917373/1000000000 : ℝ)*X 2 1+(2015676639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1871015525733589050582286617/363125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78927903/10000000000000 : ℝ)*(base19) + (105074597/20000000000000 : ℝ)*(base23) + (13843021/20000000000000 : ℝ)*(lower2) + (81569517/50000000000000 : ℝ)*(upper3) + (58245399/100000000000000 : ℝ)*(upper5) + (683323831197391/25000000000000 : ℝ)*(major0) + (683323831197391/25000000000000 : ℝ)*(major1) + (683323831197391/25000000000000 : ℝ)*(major2) + (58223026730691/1562500000000 : ℝ)*(sp0) + (372628082302949/10000000000000 : ℝ)*(sp1) + (1863140543467767/50000000000000 : ℝ)*(sp2) + (1740303872617983/100000000000000 : ℝ)*(sp3) + (987693037/12500000000000 : ℝ)*(sp4) + (4992901337/100000000000000 : ℝ)*(sp7) + (43507721637983/2500000000000 : ℝ)*(f.failure) + (93157040307713/2500000000000 : ℝ)*(f.sum) + (37065689128567/14525000000000000000000000000 : ℝ)*base65 + (3842759988377979461/726250000000000000000000000000000 : ℝ)*base68 + (8723947215780479461/726250000000000000000000000000000 : ℝ)*base70 + (2815602985883270539/726250000000000000000000000000000 : ℝ)*base71 + (4095304526973/3631250000000000000000000000 : ℝ)*base73 + (6978461359347979461/726250000000000000000000000000000 : ℝ)*base76 + (5639679095178270539/726250000000000000000000000000000 : ℝ)*base77 + (3147975649842979461/726250000000000000000000000000000 : ℝ)*base80 + (22915693583779/7262500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (654997/250000000000000000000 : ℝ)*base89 + (654997/250000000000000000000 : ℝ)*base91 + (654997/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1462775665647841396373349171/363125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (568994277/100000000000000 : ℝ)*(base19) + (2260391253/100000000000000 : ℝ)*(base23) + (87752803/100000000000000 : ℝ)*(lower2) + (73454649/50000000000000 : ℝ)*(upper3) + (100562163/50000000000000 : ℝ)*(lower4) + (2765987927815289/100000000000000 : ℝ)*(major0) + (2765987927815289/100000000000000 : ℝ)*(major1) + (276598792781529/10000000000000 : ℝ)*(major2) + (35772297097/100000000000000 : ℝ)*(sp2) + (167111269/100000000000000 : ℝ)*(sp3) + (3770851239473493/100000000000000 : ℝ)*(sp4) + (235678166904951/6250000000000 : ℝ)*(sp5) + (1885406603392571/50000000000000 : ℝ)*(sp6) + (1761124314769211/100000000000000 : ℝ)*(sp7) + (11007028011753/625000000000 : ℝ)*(f.failure) + (3770851239473493/100000000000000 : ℝ)*(f.sum) + (26820889109563/29050000000000000000000000000 : ℝ)*base66 + (8572172247607323181/2905000000000000000000000000000000 : ℝ)*base67 + (3762677824665282141/290500000000000000000000000000000 : ℝ)*base69 + (7363830557562323181/2905000000000000000000000000000000 : ℝ)*base71 + (22550973318437/29050000000000000000000000000 : ℝ)*base73 + (3755234042497782141/290500000000000000000000000000000 : ℝ)*base75 + (13499640348222023181/2905000000000000000000000000000000 : ℝ)*base77 + (31616739114177023181/2905000000000000000000000000000000 : ℝ)*base79 + (9658879867923/3631250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (257573/62500000000000000000 : ℝ)*base90 + (257573/62500000000000000000 : ℝ)*base92 + (882573/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1401_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4759/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (927/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1401_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1401_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1401_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1401_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
