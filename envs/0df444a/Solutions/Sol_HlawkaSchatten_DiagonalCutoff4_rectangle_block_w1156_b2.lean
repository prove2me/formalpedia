-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:56.414914+00:00
-- url     : https://prove2.me/submissions/c85c8f39-422d-4573-b95a-480a8515e36a

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
theorem support_rectangle_w1156_s6_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160178071/10000000000 : ℝ)*x 0 + (674137779/1250000000 : ℝ)*x 1 + (2632830873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160178071/10000000000 : ℝ)^8349 ≤ (2625488799897/20000000000000 : ℝ)^6301 := by
    have hnat : (2160178071 : ℕ)^8349*20000000000000^6301 ≤ 2625488799897^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160178071 10000000000 2625488799897 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674137779/1250000000 : ℝ)^8349 ≤ (44124395365819/100000000000000 : ℝ)^6301 := by
    have hnat : (674137779 : ℕ)^8349*100000000000000^6301 ≤ 44124395365819^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674137779 1250000000 44124395365819 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632830873/5000000000 : ℝ)^8349 ≤ (42748160629209/100000000000000 : ℝ)^6301 := by
    have hnat : (2632830873 : ℕ)^8349*100000000000000^6301 ≤ 42748160629209^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632830873 5000000000 42748160629209 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160178071/10000000000 : ℝ), (674137779/1250000000 : ℝ), (2632830873/5000000000 : ℝ)] ![(2625488799897/20000000000000 : ℝ), (44124395365819/100000000000000 : ℝ), (42748160629209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160178071/10000000000 : ℝ)|^8349 ≤ (2625488799897/20000000000000 : ℝ)^6301
        have hw : |(-2160178071/10000000000 : ℝ)|=(2160178071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674137779/1250000000 : ℝ)|^8349 ≤ (44124395365819/100000000000000 : ℝ)^6301
        have hw : |(674137779/1250000000 : ℝ)|=(674137779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632830873/5000000000 : ℝ)|^8349 ≤ (42748160629209/100000000000000 : ℝ)^6301
        have hw : |(2632830873/5000000000 : ℝ)|=(2632830873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672393353/5000000000 : ℝ)*x 0 + (-1112409607/5000000000 : ℝ)*x 1 + (526566177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672393353/5000000000 : ℝ)^8349 ≤ (8720275200803/20000000000000 : ℝ)^6301 := by
    have hnat : (2672393353 : ℕ)^8349*20000000000000^6301 ≤ 8720275200803^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672393353 5000000000 8720275200803 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112409607/5000000000 : ℝ)^8349 ≤ (106644242847/781250000000 : ℝ)^6301 := by
    have hnat : (1112409607 : ℕ)^8349*781250000000^6301 ≤ 106644242847^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112409607 5000000000 106644242847 781250000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526566177/1000000000 : ℝ)^8349 ≤ (341985287099/800000000000 : ℝ)^6301 := by
    have hnat : (526566177 : ℕ)^8349*800000000000^6301 ≤ 341985287099^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526566177 1000000000 341985287099 800000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672393353/5000000000 : ℝ), (-1112409607/5000000000 : ℝ), (526566177/1000000000 : ℝ)] ![(8720275200803/20000000000000 : ℝ), (106644242847/781250000000 : ℝ), (341985287099/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672393353/5000000000 : ℝ)|^8349 ≤ (8720275200803/20000000000000 : ℝ)^6301
        have hw : |(2672393353/5000000000 : ℝ)|=(2672393353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1112409607/5000000000 : ℝ)|^8349 ≤ (106644242847/781250000000 : ℝ)^6301
        have hw : |(-1112409607/5000000000 : ℝ)|=(1112409607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526566177/1000000000 : ℝ)|^8349 ≤ (341985287099/800000000000 : ℝ)^6301
        have hw : |(526566177/1000000000 : ℝ)|=(526566177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672393429/5000000000 : ℝ)*x 0 + (2632830833/5000000000 : ℝ)*x 1 + (-2224819151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672393429/5000000000 : ℝ)^8349 ≤ (43601377647019/100000000000000 : ℝ)^6301 := by
    have hnat : (2672393429 : ℕ)^8349*100000000000000^6301 ≤ 43601377647019^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672393429 5000000000 43601377647019 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632830833/5000000000 : ℝ)^8349 ≤ (10687039942163/25000000000000 : ℝ)^6301 := by
    have hnat : (2632830833 : ℕ)^8349*25000000000000^6301 ≤ 10687039942163^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632830833 5000000000 10687039942163 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224819151/10000000000 : ℝ)^8349 ≤ (6825231286121/50000000000000 : ℝ)^6301 := by
    have hnat : (2224819151 : ℕ)^8349*50000000000000^6301 ≤ 6825231286121^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224819151 10000000000 6825231286121 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672393429/5000000000 : ℝ), (2632830833/5000000000 : ℝ), (-2224819151/10000000000 : ℝ)] ![(43601377647019/100000000000000 : ℝ), (10687039942163/25000000000000 : ℝ), (6825231286121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672393429/5000000000 : ℝ)|^8349 ≤ (43601377647019/100000000000000 : ℝ)^6301
        have hw : |(2672393429/5000000000 : ℝ)|=(2672393429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632830833/5000000000 : ℝ)|^8349 ≤ (10687039942163/25000000000000 : ℝ)^6301
        have hw : |(2632830833/5000000000 : ℝ)|=(2632830833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2224819151/10000000000 : ℝ)|^8349 ≤ (6825231286121/50000000000000 : ℝ)^6301
        have hw : |(-2224819151/10000000000 : ℝ)|=(2224819151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090672229/2500000000 : ℝ)*x 0 + (4237407329/10000000000 : ℝ)*x 1 + (4491643539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090672229/2500000000 : ℝ)^8349 ≤ (33316883585911/100000000000000 : ℝ)^6301 := by
    have hnat : (1090672229 : ℕ)^8349*100000000000000^6301 ≤ 33316883585911^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090672229 2500000000 33316883585911 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237407329/10000000000 : ℝ)^8349 ≤ (32055121406403/100000000000000 : ℝ)^6301 := by
    have hnat : (4237407329 : ℕ)^8349*100000000000000^6301 ≤ 32055121406403^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237407329 10000000000 32055121406403 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491643539/10000000000 : ℝ)^8349 ≤ (1385119799641/4000000000000 : ℝ)^6301 := by
    have hnat : (4491643539 : ℕ)^8349*4000000000000^6301 ≤ 1385119799641^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491643539 10000000000 1385119799641 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090672229/2500000000 : ℝ), (4237407329/10000000000 : ℝ), (4491643539/10000000000 : ℝ)] ![(33316883585911/100000000000000 : ℝ), (32055121406403/100000000000000 : ℝ), (1385119799641/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090672229/2500000000 : ℝ)|^8349 ≤ (33316883585911/100000000000000 : ℝ)^6301
        have hw : |(1090672229/2500000000 : ℝ)|=(1090672229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237407329/10000000000 : ℝ)|^8349 ≤ (32055121406403/100000000000000 : ℝ)^6301
        have hw : |(4237407329/10000000000 : ℝ)|=(4237407329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491643539/10000000000 : ℝ)|^8349 ≤ (1385119799641/4000000000000 : ℝ)^6301
        have hw : |(4491643539/10000000000 : ℝ)|=(4491643539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080091533/5000000000 : ℝ)*x 0 + (658247947/1250000000 : ℝ)*x 1 + (674097397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080091533/5000000000 : ℝ)^8349 ≤ (13127484220337/100000000000000 : ℝ)^6301 := by
    have hnat : (1080091533 : ℕ)^8349*100000000000000^6301 ≤ 13127484220337^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080091533 5000000000 13127484220337 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658247947/1250000000 : ℝ)^8349 ≤ (5343952821907/12500000000000 : ℝ)^6301 := by
    have hnat : (658247947 : ℕ)^8349*12500000000000^6301 ≤ 5343952821907^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658247947 1250000000 5343952821907 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674097397/1250000000 : ℝ)^8349 ≤ (22060446592039/50000000000000 : ℝ)^6301 := by
    have hnat : (674097397 : ℕ)^8349*50000000000000^6301 ≤ 22060446592039^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674097397 1250000000 22060446592039 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080091533/5000000000 : ℝ), (658247947/1250000000 : ℝ), (674097397/1250000000 : ℝ)] ![(13127484220337/100000000000000 : ℝ), (5343952821907/12500000000000 : ℝ), (22060446592039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080091533/5000000000 : ℝ)|^8349 ≤ (13127484220337/100000000000000 : ℝ)^6301
        have hw : |(-1080091533/5000000000 : ℝ)|=(1080091533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658247947/1250000000 : ℝ)|^8349 ≤ (5343952821907/12500000000000 : ℝ)^6301
        have hw : |(658247947/1250000000 : ℝ)|=(658247947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674097397/1250000000 : ℝ)|^8349 ≤ (22060446592039/50000000000000 : ℝ)^6301
        have hw : |(674097397/1250000000 : ℝ)|=(674097397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328116471/2500000000 : ℝ)*x 0 + (-2097701657/10000000000 : ℝ)*x 1 + (5392779167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328116471/2500000000 : ℝ)^8349 ≤ (10813089144357/25000000000000 : ℝ)^6301 := by
    have hnat : (1328116471 : ℕ)^8349*25000000000000^6301 ≤ 10813089144357^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328116471 2500000000 10813089144357 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097701657/10000000000 : ℝ)^8349 ≤ (12626750330047/100000000000000 : ℝ)^6301 := by
    have hnat : (2097701657 : ℕ)^8349*100000000000000^6301 ≤ 12626750330047^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097701657 10000000000 12626750330047 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392779167/10000000000 : ℝ)^8349 ≤ (2757555817907/6250000000000 : ℝ)^6301 := by
    have hnat : (5392779167 : ℕ)^8349*6250000000000^6301 ≤ 2757555817907^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392779167 10000000000 2757555817907 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328116471/2500000000 : ℝ), (-2097701657/10000000000 : ℝ), (5392779167/10000000000 : ℝ)] ![(10813089144357/25000000000000 : ℝ), (12626750330047/100000000000000 : ℝ), (2757555817907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328116471/2500000000 : ℝ)|^8349 ≤ (10813089144357/25000000000000 : ℝ)^6301
        have hw : |(1328116471/2500000000 : ℝ)|=(1328116471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097701657/10000000000 : ℝ)|^8349 ≤ (12626750330047/100000000000000 : ℝ)^6301
        have hw : |(-2097701657/10000000000 : ℝ)|=(2097701657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392779167/10000000000 : ℝ)|^8349 ≤ (2757555817907/6250000000000 : ℝ)^6301
        have hw : |(5392779167/10000000000 : ℝ)|=(5392779167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312465869/10000000000 : ℝ)*x 0 + (5392779167/10000000000 : ℝ)*x 1 + (-524425419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312465869/10000000000 : ℝ)^8349 ≤ (43252356415609/100000000000000 : ℝ)^6301 := by
    have hnat : (5312465869 : ℕ)^8349*100000000000000^6301 ≤ 43252356415609^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312465869 10000000000 43252356415609 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392779167/10000000000 : ℝ)^8349 ≤ (2757555817907/6250000000000 : ℝ)^6301 := by
    have hnat : (5392779167 : ℕ)^8349*6250000000000^6301 ≤ 2757555817907^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392779167 10000000000 2757555817907 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524425419/2500000000 : ℝ)^8349 ≤ (12626750481587/100000000000000 : ℝ)^6301 := by
    have hnat : (524425419 : ℕ)^8349*100000000000000^6301 ≤ 12626750481587^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524425419 2500000000 12626750481587 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312465869/10000000000 : ℝ), (5392779167/10000000000 : ℝ), (-524425419/2500000000 : ℝ)] ![(43252356415609/100000000000000 : ℝ), (2757555817907/6250000000000 : ℝ), (12626750481587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312465869/10000000000 : ℝ)|^8349 ≤ (43252356415609/100000000000000 : ℝ)^6301
        have hw : |(5312465869/10000000000 : ℝ)|=(5312465869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392779167/10000000000 : ℝ)|^8349 ≤ (2757555817907/6250000000000 : ℝ)^6301
        have hw : |(5392779167/10000000000 : ℝ)|=(5392779167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524425419/2500000000 : ℝ)|^8349 ≤ (12626750481587/100000000000000 : ℝ)^6301
        have hw : |(-524425419/2500000000 : ℝ)|=(524425419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s6_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872539709/2000000000 : ℝ)*x 0 + (4491001391/10000000000 : ℝ)*x 1 + (2119026001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872539709/2000000000 : ℝ)^8349 ≤ (33316981021239/100000000000000 : ℝ)^6301 := by
    have hnat : (872539709 : ℕ)^8349*100000000000000^6301 ≤ 33316981021239^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872539709 2000000000 33316981021239 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491001391/10000000000 : ℝ)^8349 ≤ (34621435470611/100000000000000 : ℝ)^6301 := by
    have hnat : (4491001391 : ℕ)^8349*100000000000000^6301 ≤ 34621435470611^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491001391 10000000000 34621435470611 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119026001/5000000000 : ℝ)^8349 ≤ (16030791743817/50000000000000 : ℝ)^6301 := by
    have hnat : (2119026001 : ℕ)^8349*50000000000000^6301 ≤ 16030791743817^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119026001 5000000000 16030791743817 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872539709/2000000000 : ℝ), (4491001391/10000000000 : ℝ), (2119026001/5000000000 : ℝ)] ![(33316981021239/100000000000000 : ℝ), (34621435470611/100000000000000 : ℝ), (16030791743817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872539709/2000000000 : ℝ)|^8349 ≤ (33316981021239/100000000000000 : ℝ)^6301
        have hw : |(872539709/2000000000 : ℝ)|=(872539709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491001391/10000000000 : ℝ)|^8349 ≤ (34621435470611/100000000000000 : ℝ)^6301
        have hw : |(4491001391/10000000000 : ℝ)|=(4491001391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119026001/5000000000 : ℝ)|^8349 ≤ (16030791743817/50000000000000 : ℝ)^6301
        have hw : |(2119026001/5000000000 : ℝ)|=(2119026001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (879/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1417/12500 : ℝ) ^ (2087/512 : ℝ) ≤ (874371109021693/6250000000000000000 : ℝ) := by
    have hpowers : (1417/12500 : ℝ)^2087 ≤ (874371109021693/6250000000000000000 : ℝ)^512 := by
      have hnat : (1417 : ℕ)^2087*6250000000000000000^512 ≤ 874371109021693^512*12500^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1417 12500 874371109021693 6250000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1417/12500 : ℝ)) (X := (874371109021693/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (2087/512 : ℝ) ≤ (33997189224197897/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^2087 ≤ (33997189224197897/100000000000000000000 : ℝ)^512 := by
      have hnat : (2819 : ℕ)^2087*100000000000000000000^512 ≤ 33997189224197897^512*20000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 33997189224197897 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (33997189224197897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125874371109021693/3125000000000000000 : ℝ) ≤ (1250085794106479/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (3125874371109021693/3125000000000000000 : ℝ)^512 ≤ (1250085794106479/1250000000000000 : ℝ)^2087 := by
      have hnat : (3125874371109021693 : ℕ)^512*1250000000000000^2087 ≤ 1250085794106479^2087*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125874371109021693 3125000000000000000 1250085794106479 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250085794106479/1250000000000000 : ℝ)) (X := (3125874371109021693/3125000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009597425393708997/20000000000000000000 : ℝ) ≤ (10001177046545669/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (20009597425393708997/20000000000000000000 : ℝ)^512 ≤ (10001177046545669/10000000000000000 : ℝ)^2087 := by
      have hnat : (20009597425393708997 : ℕ)^512*10000000000000000^2087 ≤ 10001177046545669^2087*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009597425393708997 20000000000000000000 10001177046545669 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177046545669/10000000000000000 : ℝ)) (X := (20009597425393708997/20000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033997189224197897/50000000000000000000 : ℝ) ≤ (5000833870119753/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50033997189224197897/50000000000000000000 : ℝ)^512 ≤ (5000833870119753/5000000000000000 : ℝ)^2087 := by
      have hnat : (50033997189224197897 : ℕ)^512*5000000000000000^2087 ≤ 5000833870119753^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033997189224197897 50000000000000000000 5000833870119753 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000833870119753/5000000000000000 : ℝ)) (X := (50033997189224197897/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(874371109021693/6250000000000000000 : ℝ) ≤ ((3447596080011441503/3448750000000000000 : ℝ)+2*(490693693837/275900000000000 : ℝ)*(1417/12500 : ℝ))^(2087/512 : ℝ) := by
    rw [show (3447596080011441503/3448750000000000000 : ℝ)+2*(490693693837/275900000000000 : ℝ)*(1417/12500 : ℝ)=(1250085794106479/1250000000000000 : ℝ) by norm_num, show 1+2*(874371109021693/6250000000000000000 : ℝ)=(3125874371109021693/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33997189224197897/100000000000000000000 : ℝ)+(874371109021693/6250000000000000000 : ℝ) ≤ ((3447596080011441503/3448750000000000000 : ℝ)+(490693693837/275900000000000 : ℝ)*((2819/20000 : ℝ)+(1417/12500 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (3447596080011441503/3448750000000000000 : ℝ)+(490693693837/275900000000000 : ℝ)*((2819/20000 : ℝ)+(1417/12500 : ℝ))=(10001177046545669/10000000000000000 : ℝ) by norm_num, show 1+(33997189224197897/100000000000000000000 : ℝ)+(874371109021693/6250000000000000000 : ℝ)=(20009597425393708997/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33997189224197897/100000000000000000000 : ℝ) ≤ ((3447596080011441503/3448750000000000000 : ℝ)+2*(490693693837/275900000000000 : ℝ)*(2819/20000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (3447596080011441503/3448750000000000000 : ℝ)+2*(490693693837/275900000000000 : ℝ)*(2819/20000 : ℝ)=(5000833870119753/5000000000000000 : ℝ) by norm_num, show 1+2*(33997189224197897/100000000000000000000 : ℝ)=(50033997189224197897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3447596080011441503/3448750000000000000 : ℝ)*(X 1 0+X 2 0)+(490693693837/275900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3447596080011441503/3448750000000000000 : ℝ)) (alpha := (490693693837/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3447596080011441503/3448750000000000000 : ℝ)*(X 0 1+X 2 1)+(490693693837/275900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3447596080011441503/3448750000000000000 : ℝ)) (alpha := (490693693837/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3447596080011441503/3448750000000000000 : ℝ)*(X 0 2+X 1 2)+(490693693837/275900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3447596080011441503/3448750000000000000 : ℝ)) (alpha := (490693693837/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2160178071/10000000000 : ℝ)*X 0 0+(674137779/1250000000 : ℝ)*X 0 1+(2632830873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672393353/5000000000 : ℝ)*X 1 0+(-1112409607/5000000000 : ℝ)*X 1 1+(526566177/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672393429/5000000000 : ℝ)*X 2 0+(2632830833/5000000000 : ℝ)*X 2 1+(-2224819151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090672229/2500000000 : ℝ)*X 0 0+(4237407329/10000000000 : ℝ)*X 0 1+(4491643539/10000000000 : ℝ)*X 0 2+(1090672229/2500000000 : ℝ)*X 1 0+(4237407329/10000000000 : ℝ)*X 1 1+(4491643539/10000000000 : ℝ)*X 1 2+(1090672229/2500000000 : ℝ)*X 2 0+(4237407329/10000000000 : ℝ)*X 2 1+(4491643539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080091533/5000000000 : ℝ)*X 0 0+(658247947/1250000000 : ℝ)*X 0 1+(674097397/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328116471/2500000000 : ℝ)*X 1 0+(-2097701657/10000000000 : ℝ)*X 1 1+(5392779167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312465869/10000000000 : ℝ)*X 2 0+(5392779167/10000000000 : ℝ)*X 2 1+(-524425419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872539709/2000000000 : ℝ)*X 0 0+(4491001391/10000000000 : ℝ)*X 0 1+(2119026001/5000000000 : ℝ)*X 0 2+(872539709/2000000000 : ℝ)*X 1 0+(4491001391/10000000000 : ℝ)*X 1 1+(2119026001/5000000000 : ℝ)*X 1 2+(872539709/2000000000 : ℝ)*X 2 0+(4491001391/10000000000 : ℝ)*X 2 1+(2119026001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4235306000011907089863621/1077734375000000000000000000000 : ℝ) := by norm_num
    linear_combination (131352221/20000000000000 : ℝ)*(base19) + (147414971/25000000000000 : ℝ)*(base23) + (155135937/100000000000000 : ℝ)*(lower2) + (33776191/25000000000000 : ℝ)*(upper3) + (63767149/100000000000000 : ℝ)*(upper5) + (294504870663401/5000000000000 : ℝ)*(major0) + (294504870663401/5000000000000 : ℝ)*(major1) + (294504870663401/5000000000000 : ℝ)*(major2) + (1569362378770907/20000000000000 : ℝ)*(sp0) + (7846826550535839/100000000000000 : ℝ)*(sp1) + (7846826617637061/100000000000000 : ℝ)*(sp2) + (1966678320874301/50000000000000 : ℝ)*(sp3) + (1531344241/10000000000000 : ℝ)*(sp4) + (5423248181/50000000000000 : ℝ)*(sp7) + (786673497648993/20000000000000 : ℝ)*(f.failure) + (490426700456059/6250000000000 : ℝ)*(f.sum) + (3358409481541/551800000000000000000000000 : ℝ)*base65 + (108004359870755797/17243750000000000000000000000000 : ℝ)*base68 + (125828320535305797/17243750000000000000000000000000 : ℝ)*base70 + (215005642524405797/17243750000000000000000000000000 : ℝ)*base72 + (4428615671281/1379500000000000000000000000 : ℝ)*base73 + (366035805621944203/17243750000000000000000000000000 : ℝ)*base75 + (131938843168380797/17243750000000000000000000000000 : ℝ)*base78 + (86189694318343297/17243750000000000000000000000000 : ℝ)*base80 + (1376757532621/2759000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1817573/2000000000000000000000 : ℝ)*base90 + (1817573/2000000000000000000000 : ℝ)*base92 + (1817573/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60686367739616554397487/13795000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224608183/25000000000000 : ℝ)*(base19) + (919823391/100000000000000 : ℝ)*(base23) + (1736553/2000000000000 : ℝ)*(upper3) + (26435487/100000000000000 : ℝ)*(lower4) + (112278021/100000000000000 : ℝ)*(upper5) + (5920034235141589/100000000000000 : ℝ)*(major0) + (5920034235141589/100000000000000 : ℝ)*(major1) + (5920034235141589/100000000000000 : ℝ)*(major2) + (503474927/2000000000000 : ℝ)*(sp1) + (6042660739/25000000000000 : ℝ)*(sp2) + (788670922684091/10000000000000 : ℝ)*(sp4) + (7886683154661827/100000000000000 : ℝ)*(sp5) + (3943342068187281/50000000000000 : ℝ)*(sp6) + (3953359096803701/100000000000000 : ℝ)*(sp7) + (3953359096803701/100000000000000 : ℝ)*(f.failure) + (788670922684091/10000000000000 : ℝ)*(f.sum) + (25582797340541/6897500000000000000000000000 : ℝ)*base66 + (451074730030244233/344875000000000000000000000000000 : ℝ)*base68 + (935902526411369233/344875000000000000000000000000000 : ℝ)*base70 + (6067371101325005767/344875000000000000000000000000000 : ℝ)*base71 + (67509177711347/13795000000000000000000000000 : ℝ)*base74 + (1879103732885244233/344875000000000000000000000000000 : ℝ)*base76 + (2800279366247255767/344875000000000000000000000000000 : ℝ)*base77 + (2852972482968505767/344875000000000000000000000000000 : ℝ)*base79 + (65175219346537/13795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8621239/10000000000000000000000 : ℝ)*base89 + (8621239/10000000000000000000000 : ℝ)*base91 + (8621239/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s7_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-216020651/1000000000 : ℝ)*x 0 + (1078559731/2000000000 : ℝ)*x 1 + (5265946397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216020651/1000000000 : ℝ)^8349 ≤ (3281918249261/25000000000000 : ℝ)^6301 := by
    have hnat : (216020651 : ℕ)^8349*25000000000000^6301 ≤ 3281918249261^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216020651 1000000000 3281918249261 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078559731/2000000000 : ℝ)^8349 ≤ (5515138043733/12500000000000 : ℝ)^6301 := by
    have hnat : (1078559731 : ℕ)^8349*12500000000000^6301 ≤ 5515138043733^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078559731 2000000000 5515138043733 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265946397/10000000000 : ℝ)^8349 ≤ (10687805658711/25000000000000 : ℝ)^6301 := by
    have hnat : (5265946397 : ℕ)^8349*25000000000000^6301 ≤ 10687805658711^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265946397 10000000000 10687805658711 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216020651/1000000000 : ℝ), (1078559731/2000000000 : ℝ), (5265946397/10000000000 : ℝ)] ![(3281918249261/25000000000000 : ℝ), (5515138043733/12500000000000 : ℝ), (10687805658711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216020651/1000000000 : ℝ)|^8349 ≤ (3281918249261/25000000000000 : ℝ)^6301
        have hw : |(-216020651/1000000000 : ℝ)|=(216020651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078559731/2000000000 : ℝ)|^8349 ≤ (5515138043733/12500000000000 : ℝ)^6301
        have hw : |(1078559731/2000000000 : ℝ)|=(1078559731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265946397/10000000000 : ℝ)|^8349 ≤ (10687805658711/25000000000000 : ℝ)^6301
        have hw : |(5265946397/10000000000 : ℝ)|=(5265946397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344709617/10000000000 : ℝ)*x 0 + (-2224544673/10000000000 : ℝ)*x 1 + (5265946717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344709617/10000000000 : ℝ)^8349 ≤ (1090013568329/2500000000000 : ℝ)^6301 := by
    have hnat : (5344709617 : ℕ)^8349*2500000000000^6301 ≤ 1090013568329^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344709617 10000000000 1090013568329 2500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224544673/10000000000 : ℝ)^8349 ≤ (545929247087/4000000000000 : ℝ)^6301 := by
    have hnat : (2224544673 : ℕ)^8349*4000000000000^6301 ≤ 545929247087^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224544673 10000000000 545929247087 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265946717/10000000000 : ℝ)^8349 ≤ (42751226077131/100000000000000 : ℝ)^6301 := by
    have hnat : (5265946717 : ℕ)^8349*100000000000000^6301 ≤ 42751226077131^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265946717 10000000000 42751226077131 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344709617/10000000000 : ℝ), (-2224544673/10000000000 : ℝ), (5265946717/10000000000 : ℝ)] ![(1090013568329/2500000000000 : ℝ), (545929247087/4000000000000 : ℝ), (42751226077131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344709617/10000000000 : ℝ)|^8349 ≤ (1090013568329/2500000000000 : ℝ)^6301
        have hw : |(5344709617/10000000000 : ℝ)|=(5344709617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224544673/10000000000 : ℝ)|^8349 ≤ (545929247087/4000000000000 : ℝ)^6301
        have hw : |(-2224544673/10000000000 : ℝ)|=(2224544673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265946717/10000000000 : ℝ)|^8349 ≤ (42751226077131/100000000000000 : ℝ)^6301
        have hw : |(5265946717/10000000000 : ℝ)|=(5265946717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344710173/10000000000 : ℝ)*x 0 + (2632973101/5000000000 : ℝ)*x 1 + (-278068077/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344710173/10000000000 : ℝ)^8349 ≤ (5450068592883/12500000000000 : ℝ)^6301 := by
    have hnat : (5344710173 : ℕ)^8349*12500000000000^6301 ≤ 5450068592883^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344710173 10000000000 5450068592883 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632973101/5000000000 : ℝ)^8349 ≤ (106878051343/250000000000 : ℝ)^6301 := by
    have hnat : (2632973101 : ℕ)^8349*250000000000^6301 ≤ 106878051343^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632973101 5000000000 106878051343 250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278068077/1250000000 : ℝ)^8349 ≤ (13648230713797/100000000000000 : ℝ)^6301 := by
    have hnat : (278068077 : ℕ)^8349*100000000000000^6301 ≤ 13648230713797^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278068077 1250000000 13648230713797 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344710173/10000000000 : ℝ), (2632973101/5000000000 : ℝ), (-278068077/1250000000 : ℝ)] ![(5450068592883/12500000000000 : ℝ), (106878051343/250000000000 : ℝ), (13648230713797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344710173/10000000000 : ℝ)|^8349 ≤ (5450068592883/12500000000000 : ℝ)^6301
        have hw : |(5344710173/10000000000 : ℝ)|=(5344710173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632973101/5000000000 : ℝ)|^8349 ≤ (106878051343/250000000000 : ℝ)^6301
        have hw : |(2632973101/5000000000 : ℝ)|=(2632973101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278068077/1250000000 : ℝ)|^8349 ≤ (13648230713797/100000000000000 : ℝ)^6301
        have hw : |(-278068077/1250000000 : ℝ)|=(278068077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181351831/5000000000 : ℝ)*x 0 + (4237992699/10000000000 : ℝ)*x 1 + (4491054519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181351831/5000000000 : ℝ)^8349 ≤ (4164629099989/12500000000000 : ℝ)^6301 := by
    have hnat : (2181351831 : ℕ)^8349*12500000000000^6301 ≤ 4164629099989^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181351831 5000000000 4164629099989 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237992699/10000000000 : ℝ)^8349 ≤ (32060989032141/100000000000000 : ℝ)^6301 := by
    have hnat : (4237992699 : ℕ)^8349*100000000000000^6301 ≤ 32060989032141^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237992699 10000000000 32060989032141 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491054519/10000000000 : ℝ)^8349 ≤ (34621978159793/100000000000000 : ℝ)^6301 := by
    have hnat : (4491054519 : ℕ)^8349*100000000000000^6301 ≤ 34621978159793^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491054519 10000000000 34621978159793 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181351831/5000000000 : ℝ), (4237992699/10000000000 : ℝ), (4491054519/10000000000 : ℝ)] ![(4164629099989/12500000000000 : ℝ), (32060989032141/100000000000000 : ℝ), (34621978159793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181351831/5000000000 : ℝ)|^8349 ≤ (4164629099989/12500000000000 : ℝ)^6301
        have hw : |(2181351831/5000000000 : ℝ)|=(2181351831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237992699/10000000000 : ℝ)|^8349 ≤ (32060989032141/100000000000000 : ℝ)^6301
        have hw : |(4237992699/10000000000 : ℝ)|=(4237992699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491054519/10000000000 : ℝ)|^8349 ≤ (34621978159793/100000000000000 : ℝ)^6301
        have hw : |(4491054519/10000000000 : ℝ)|=(4491054519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432042221/2000000000 : ℝ)*x 0 + (5266265533/10000000000 : ℝ)*x 1 + (33702991/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432042221/2000000000 : ℝ)^8349 ≤ (3281927499291/25000000000000 : ℝ)^6301 := by
    have hnat : (432042221 : ℕ)^8349*25000000000000^6301 ≤ 3281927499291^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432042221 2000000000 3281927499291 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266265533/10000000000 : ℝ)^8349 ≤ (42754655661389/100000000000000 : ℝ)^6301 := by
    have hnat : (5266265533 : ℕ)^8349*100000000000000^6301 ≤ 42754655661389^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266265533 10000000000 42754655661389 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33702991/62500000 : ℝ)^8349 ≤ (44117634330879/100000000000000 : ℝ)^6301 := by
    have hnat : (33702991 : ℕ)^8349*100000000000000^6301 ≤ 44117634330879^6301*62500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33702991 62500000 44117634330879 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432042221/2000000000 : ℝ), (5266265533/10000000000 : ℝ), (33702991/62500000 : ℝ)] ![(3281927499291/25000000000000 : ℝ), (42754655661389/100000000000000 : ℝ), (44117634330879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432042221/2000000000 : ℝ)|^8349 ≤ (3281927499291/25000000000000 : ℝ)^6301
        have hw : |(-432042221/2000000000 : ℝ)|=(432042221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266265533/10000000000 : ℝ)|^8349 ≤ (42754655661389/100000000000000 : ℝ)^6301
        have hw : |(5266265533/10000000000 : ℝ)|=(5266265533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33702991/62500000 : ℝ)|^8349 ≤ (44117634330879/100000000000000 : ℝ)^6301
        have hw : |(33702991/62500000 : ℝ)|=(33702991/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312538047/10000000000 : ℝ)*x 0 + (-1049006299/5000000000 : ℝ)*x 1 + (5392478579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312538047/10000000000 : ℝ)^8349 ≤ (10813283767351/25000000000000 : ℝ)^6301 := by
    have hnat : (5312538047 : ℕ)^8349*25000000000000^6301 ≤ 10813283767351^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312538047 10000000000 10813283767351 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049006299/5000000000 : ℝ)^8349 ≤ (1262923038501/10000000000000 : ℝ)^6301 := by
    have hnat : (1049006299 : ℕ)^8349*10000000000000^6301 ≤ 1262923038501^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049006299 5000000000 1262923038501 10000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392478579/10000000000 : ℝ)^8349 ≤ (2757352158553/6250000000000 : ℝ)^6301 := by
    have hnat : (5392478579 : ℕ)^8349*6250000000000^6301 ≤ 2757352158553^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392478579 10000000000 2757352158553 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312538047/10000000000 : ℝ), (-1049006299/5000000000 : ℝ), (5392478579/10000000000 : ℝ)] ![(10813283767351/25000000000000 : ℝ), (1262923038501/10000000000000 : ℝ), (2757352158553/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312538047/10000000000 : ℝ)|^8349 ≤ (10813283767351/25000000000000 : ℝ)^6301
        have hw : |(5312538047/10000000000 : ℝ)|=(5312538047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049006299/5000000000 : ℝ)|^8349 ≤ (1262923038501/10000000000000 : ℝ)^6301
        have hw : |(-1049006299/5000000000 : ℝ)|=(1049006299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392478579/10000000000 : ℝ)|^8349 ≤ (2757352158553/6250000000000 : ℝ)^6301
        have hw : |(5392478579/10000000000 : ℝ)|=(5392478579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328134511/2500000000 : ℝ)*x 0 + (2696239293/5000000000 : ℝ)*x 1 + (-131125787/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328134511/2500000000 : ℝ)^8349 ≤ (540664187963/1250000000000 : ℝ)^6301 := by
    have hnat : (1328134511 : ℕ)^8349*1250000000000^6301 ≤ 540664187963^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328134511 2500000000 540664187963 1250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696239293/5000000000 : ℝ)^8349 ≤ (44117634612731/100000000000000 : ℝ)^6301 := by
    have hnat : (2696239293 : ℕ)^8349*100000000000000^6301 ≤ 44117634612731^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696239293 5000000000 44117634612731 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131125787/625000000 : ℝ)^8349 ≤ (12629230337153/100000000000000 : ℝ)^6301 := by
    have hnat : (131125787 : ℕ)^8349*100000000000000^6301 ≤ 12629230337153^6301*625000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131125787 625000000 12629230337153 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328134511/2500000000 : ℝ), (2696239293/5000000000 : ℝ), (-131125787/625000000 : ℝ)] ![(540664187963/1250000000000 : ℝ), (44117634612731/100000000000000 : ℝ), (12629230337153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328134511/2500000000 : ℝ)|^8349 ≤ (540664187963/1250000000000 : ℝ)^6301
        have hw : |(1328134511/2500000000 : ℝ)|=(1328134511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696239293/5000000000 : ℝ)|^8349 ≤ (44117634612731/100000000000000 : ℝ)^6301
        have hw : |(2696239293/5000000000 : ℝ)|=(2696239293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131125787/625000000 : ℝ)|^8349 ≤ (12629230337153/100000000000000 : ℝ)^6301
        have hw : |(-131125787/625000000 : ℝ)|=(131125787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s7_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872542673/2000000000 : ℝ)*x 0 + (1122604599/2500000000 : ℝ)*x 1 + (4238631101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872542673/2000000000 : ℝ)^8349 ≤ (666342619683/2000000000000 : ℝ)^6301 := by
    have hnat : (872542673 : ℕ)^8349*2000000000000^6301 ≤ 666342619683^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872542673 2000000000 666342619683 2000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122604599/2500000000 : ℝ)^8349 ≤ (8653870115033/25000000000000 : ℝ)^6301 := by
    have hnat : (1122604599 : ℕ)^8349*25000000000000^6301 ≤ 8653870115033^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122604599 2500000000 8653870115033 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238631101/10000000000 : ℝ)^8349 ≤ (16033694269899/50000000000000 : ℝ)^6301 := by
    have hnat : (4238631101 : ℕ)^8349*50000000000000^6301 ≤ 16033694269899^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238631101 10000000000 16033694269899 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872542673/2000000000 : ℝ), (1122604599/2500000000 : ℝ), (4238631101/10000000000 : ℝ)] ![(666342619683/2000000000000 : ℝ), (8653870115033/25000000000000 : ℝ), (16033694269899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872542673/2000000000 : ℝ)|^8349 ≤ (666342619683/2000000000000 : ℝ)^6301
        have hw : |(872542673/2000000000 : ℝ)|=(872542673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122604599/2500000000 : ℝ)|^8349 ≤ (8653870115033/25000000000000 : ℝ)^6301
        have hw : |(1122604599/2500000000 : ℝ)|=(1122604599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238631101/10000000000 : ℝ)|^8349 ≤ (16033694269899/50000000000000 : ℝ)^6301
        have hw : |(4238631101/10000000000 : ℝ)|=(4238631101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (2087/512 : ℝ) ≤ (14136396365004633/100000000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^2087 ≤ (14136396365004633/100000000000000000000 : ℝ)^512 := by
      have hnat : (2273 : ℕ)^2087*100000000000000000000^512 ≤ 14136396365004633^512*20000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 14136396365004633 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (14136396365004633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (879/6250 : ℝ) ^ (2087/512 : ℝ) ≤ (16846717358202151/50000000000000000000 : ℝ) := by
    have hpowers : (879/6250 : ℝ)^2087 ≤ (16846717358202151/50000000000000000000 : ℝ)^512 := by
      have hnat : (879 : ℕ)^2087*50000000000000000000^512 ≤ 16846717358202151^512*6250^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 6250 16846717358202151 50000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/6250 : ℝ)) (X := (16846717358202151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014136396365004633/50000000000000000000 : ℝ) ≤ (10000693537413489/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50014136396365004633/50000000000000000000 : ℝ)^512 ≤ (10000693537413489/10000000000000000 : ℝ)^2087 := by
      have hnat : (50014136396365004633 : ℕ)^512*10000000000000000^2087 ≤ 10000693537413489^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014136396365004633 50000000000000000000 10000693537413489 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693537413489/10000000000000000 : ℝ)) (X := (50014136396365004633/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009565966216281787/20000000000000000000 : ℝ) ≤ (5000586594514121/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (20009565966216281787/20000000000000000000 : ℝ)^512 ≤ (5000586594514121/5000000000000000 : ℝ)^2087 := by
      have hnat : (20009565966216281787 : ℕ)^512*5000000000000000^2087 ≤ 5000586594514121^2087*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009565966216281787 20000000000000000000 5000586594514121 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000586594514121/5000000000000000 : ℝ)) (X := (20009565966216281787/20000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016846717358202151/25000000000000000000 : ℝ) ≤ (2000330568128599/2000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (25016846717358202151/25000000000000000000 : ℝ)^512 ≤ (2000330568128599/2000000000000000 : ℝ)^2087 := by
      have hnat : (25016846717358202151 : ℕ)^512*2000000000000000^2087 ≤ 2000330568128599^2087*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016846717358202151 25000000000000000000 2000330568128599 2000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000330568128599/2000000000000000 : ℝ)) (X := (25016846717358202151/25000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14136396365004633/100000000000000000000 : ℝ) ≤ ((26980969376275671121/26990000000000000000 : ℝ)+2*(479651614753/269900000000000 : ℝ)*(2273/20000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (26980969376275671121/26990000000000000000 : ℝ)+2*(479651614753/269900000000000 : ℝ)*(2273/20000 : ℝ)=(10000693537413489/10000000000000000 : ℝ) by norm_num, show 1+2*(14136396365004633/100000000000000000000 : ℝ)=(50014136396365004633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16846717358202151/50000000000000000000 : ℝ)+(14136396365004633/100000000000000000000 : ℝ) ≤ ((26980969376275671121/26990000000000000000 : ℝ)+(479651614753/269900000000000 : ℝ)*((879/6250 : ℝ)+(2273/20000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (26980969376275671121/26990000000000000000 : ℝ)+(479651614753/269900000000000 : ℝ)*((879/6250 : ℝ)+(2273/20000 : ℝ))=(5000586594514121/5000000000000000 : ℝ) by norm_num, show 1+(16846717358202151/50000000000000000000 : ℝ)+(14136396365004633/100000000000000000000 : ℝ)=(20009565966216281787/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16846717358202151/50000000000000000000 : ℝ) ≤ ((26980969376275671121/26990000000000000000 : ℝ)+2*(479651614753/269900000000000 : ℝ)*(879/6250 : ℝ))^(2087/512 : ℝ) := by
    rw [show (26980969376275671121/26990000000000000000 : ℝ)+2*(479651614753/269900000000000 : ℝ)*(879/6250 : ℝ)=(2000330568128599/2000000000000000 : ℝ) by norm_num, show 1+2*(16846717358202151/50000000000000000000 : ℝ)=(25016846717358202151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26980969376275671121/26990000000000000000 : ℝ)*(X 1 0+X 2 0)+(479651614753/269900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (26980969376275671121/26990000000000000000 : ℝ)) (alpha := (479651614753/269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26980969376275671121/26990000000000000000 : ℝ)*(X 0 1+X 2 1)+(479651614753/269900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (26980969376275671121/26990000000000000000 : ℝ)) (alpha := (479651614753/269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26980969376275671121/26990000000000000000 : ℝ)*(X 0 2+X 1 2)+(479651614753/269900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (26980969376275671121/26990000000000000000 : ℝ)) (alpha := (479651614753/269900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216020651/1000000000 : ℝ)*X 0 0+(1078559731/2000000000 : ℝ)*X 0 1+(5265946397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344709617/10000000000 : ℝ)*X 1 0+(-2224544673/10000000000 : ℝ)*X 1 1+(5265946717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344710173/10000000000 : ℝ)*X 2 0+(2632973101/5000000000 : ℝ)*X 2 1+(-278068077/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181351831/5000000000 : ℝ)*X 0 0+(4237992699/10000000000 : ℝ)*X 0 1+(4491054519/10000000000 : ℝ)*X 0 2+(2181351831/5000000000 : ℝ)*X 1 0+(4237992699/10000000000 : ℝ)*X 1 1+(4491054519/10000000000 : ℝ)*X 1 2+(2181351831/5000000000 : ℝ)*X 2 0+(4237992699/10000000000 : ℝ)*X 2 1+(4491054519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432042221/2000000000 : ℝ)*X 0 0+(5266265533/10000000000 : ℝ)*X 0 1+(33702991/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312538047/10000000000 : ℝ)*X 1 0+(-1049006299/5000000000 : ℝ)*X 1 1+(5392478579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328134511/2500000000 : ℝ)*X 2 0+(2696239293/5000000000 : ℝ)*X 2 1+(-131125787/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872542673/2000000000 : ℝ)*X 0 0+(1122604599/2500000000 : ℝ)*X 0 1+(4238631101/10000000000 : ℝ)*X 0 2+(872542673/2000000000 : ℝ)*X 1 0+(1122604599/2500000000 : ℝ)*X 1 1+(4238631101/10000000000 : ℝ)*X 1 2+(872542673/2000000000 : ℝ)*X 2 0+(1122604599/2500000000 : ℝ)*X 2 1+(4238631101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9794377268949088060371/3373750000000000000000000000 : ℝ) := by norm_num
    linear_combination (237621597/25000000000000 : ℝ)*(base19) + (143830823/10000000000000 : ℝ)*(base23) + (152284867/100000000000000 : ℝ)*(upper3) + (88791257/50000000000000 : ℝ)*(upper4) + (39053813/25000000000000 : ℝ)*(upper5) + (739680545794001/12500000000000 : ℝ)*(major0) + (739680545794001/12500000000000 : ℝ)*(major1) + (739680545794001/12500000000000 : ℝ)*(major2) + (1576643114653829/20000000000000 : ℝ)*(sp0) + (394162904281239/5000000000000 : ℝ)*(sp1) + (3941628798901469/50000000000000 : ℝ)*(sp2) + (1975806803739667/50000000000000 : ℝ)*(sp3) + (5432855253/12500000000000 : ℝ)*(sp4) + (639693723/4000000000000 : ℝ)*(sp7) + (395162959982241/10000000000000 : ℝ)*(f.failure) + (123175922439237/1562500000000 : ℝ)*(f.sum) + (35866806838589/13495000000000000000000000000 : ℝ)*base65 + (3318640421504829879/337375000000000000000000000000000 : ℝ)*base68 + (209808501231795121/337375000000000000000000000000000 : ℝ)*base69 + (1744576472528579879/337375000000000000000000000000000 : ℝ)*base72 + (29400204694577/6747500000000000000000000000 : ℝ)*base73 + (3306928194673829879/337375000000000000000000000000000 : ℝ)*base76 + (259977907623170121/337375000000000000000000000000000 : ℝ)*base77 + (533715587046295121/337375000000000000000000000000000 : ℝ)*base79 + (121186297969089/13495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4110299/1000000000000000000000 : ℝ)*base89 + (4110299/1000000000000000000000 : ℝ)*base91 + (4110299/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1114918693400950209806202117/134950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34568357/2500000000000 : ℝ)*(base19) + (1543391173/100000000000000 : ℝ)*(base23) + (165141237/100000000000000 : ℝ)*(upper3) + (14596841/20000000000000 : ℝ)*(lower4) + (157911673/100000000000000 : ℝ)*(upper5) + (1189471618149959/20000000000000 : ℝ)*(major0) + (1189471618149959/20000000000000 : ℝ)*(major1) + (1189471618149959/20000000000000 : ℝ)*(major2) + (38489155641/100000000000000 : ℝ)*(sp1) + (2691925707/6250000000000 : ℝ)*(sp2) + (7923110122067051/100000000000000 : ℝ)*(sp4) + (792307025017713/10000000000000 : ℝ)*(sp5) + (7923065507864567/100000000000000 : ℝ)*(sp6) + (1985802892020983/50000000000000 : ℝ)*(sp7) + (1985802892020983/50000000000000 : ℝ)*(f.failure) + (7923110122067051/100000000000000 : ℝ)*(f.sum) + (776487292431/1349500000000000000000000000 : ℝ)*base65 + (8972882134659865961/539800000000000000000000000000000 : ℝ)*base68 + (3040561864158465961/539800000000000000000000000000000 : ℝ)*base70 + (1810173203315734039/539800000000000000000000000000000 : ℝ)*base71 + (1942418827057/269900000000000000000000000 : ℝ)*base74 + (6768826759477065961/539800000000000000000000000000000 : ℝ)*base76 + (1277590388000865961/539800000000000000000000000000000 : ℝ)*base78 + (11253238141059265961/539800000000000000000000000000000 : ℝ)*base80 + (3025585488837/2699000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (21978963/5000000000000000000000 : ℝ)*base90 + (21978963/5000000000000000000000 : ℝ)*base92 + (21978963/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1156_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s8_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-216021053/1000000000 : ℝ)*x 0 + (2696369623/5000000000 : ℝ)*x 1 + (2633001629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216021053/1000000000 : ℝ)^8349 ≤ (2625541073423/20000000000000 : ℝ)^6301 := by
    have hnat : (216021053 : ℕ)^8349*20000000000000^6301 ≤ 2625541073423^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216021053 1000000000 2625541073423 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696369623/5000000000 : ℝ)^8349 ≤ (11030115079033/25000000000000 : ℝ)^6301 := by
    have hnat : (2696369623 : ℕ)^8349*25000000000000^6301 ≤ 11030115079033^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696369623 5000000000 11030115079033 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633001629/5000000000 : ℝ)^8349 ≤ (42751834298029/100000000000000 : ℝ)^6301 := by
    have hnat : (2633001629 : ℕ)^8349*100000000000000^6301 ≤ 42751834298029^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633001629 5000000000 42751834298029 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216021053/1000000000 : ℝ), (2696369623/5000000000 : ℝ), (2633001629/5000000000 : ℝ)] ![(2625541073423/20000000000000 : ℝ), (11030115079033/25000000000000 : ℝ), (42751834298029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216021053/1000000000 : ℝ)|^8349 ≤ (2625541073423/20000000000000 : ℝ)^6301
        have hw : |(-216021053/1000000000 : ℝ)|=(216021053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696369623/5000000000 : ℝ)|^8349 ≤ (11030115079033/25000000000000 : ℝ)^6301
        have hw : |(2696369623/5000000000 : ℝ)|=(2696369623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633001629/5000000000 : ℝ)|^8349 ≤ (42751834298029/100000000000000 : ℝ)^6301
        have hw : |(2633001629/5000000000 : ℝ)|=(2633001629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344695137/10000000000 : ℝ)*x 0 + (-1112244553/5000000000 : ℝ)*x 1 + (263300163/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344695137/10000000000 : ℝ)^8349 ≤ (21800193108149/50000000000000 : ℝ)^6301 := by
    have hnat : (5344695137 : ℕ)^8349*50000000000000^6301 ≤ 21800193108149^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344695137 10000000000 21800193108149 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112244553/5000000000 : ℝ)^8349 ≤ (13647779450843/100000000000000 : ℝ)^6301 := by
    have hnat : (1112244553 : ℕ)^8349*100000000000000^6301 ≤ 13647779450843^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112244553 5000000000 13647779450843 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263300163/500000000 : ℝ)^8349 ≤ (5343979289943/12500000000000 : ℝ)^6301 := by
    have hnat : (263300163 : ℕ)^8349*12500000000000^6301 ≤ 5343979289943^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263300163 500000000 5343979289943 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344695137/10000000000 : ℝ), (-1112244553/5000000000 : ℝ), (263300163/500000000 : ℝ)] ![(21800193108149/50000000000000 : ℝ), (13647779450843/100000000000000 : ℝ), (5343979289943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344695137/10000000000 : ℝ)|^8349 ≤ (21800193108149/50000000000000 : ℝ)^6301
        have hw : |(5344695137/10000000000 : ℝ)|=(5344695137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1112244553/5000000000 : ℝ)|^8349 ≤ (13647779450843/100000000000000 : ℝ)^6301
        have hw : |(-1112244553/5000000000 : ℝ)|=(1112244553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263300163/500000000 : ℝ)|^8349 ≤ (5343979289943/12500000000000 : ℝ)^6301
        have hw : |(263300163/500000000 : ℝ)|=(263300163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668086891/1250000000 : ℝ)*x 0 + (5266003251/10000000000 : ℝ)*x 1 + (-2224489131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668086891/1250000000 : ℝ)^8349 ≤ (8720077223803/20000000000000 : ℝ)^6301 := by
    have hnat : (668086891 : ℕ)^8349*20000000000000^6301 ≤ 8720077223803^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668086891 1250000000 8720077223803 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266003251/10000000000 : ℝ)^8349 ≤ (42751834222729/100000000000000 : ℝ)^6301 := by
    have hnat : (5266003251 : ℕ)^8349*100000000000000^6301 ≤ 42751834222729^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266003251 10000000000 42751834222729 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224489131/10000000000 : ℝ)^8349 ≤ (13647779654077/100000000000000 : ℝ)^6301 := by
    have hnat : (2224489131 : ℕ)^8349*100000000000000^6301 ≤ 13647779654077^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224489131 10000000000 13647779654077 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668086891/1250000000 : ℝ), (5266003251/10000000000 : ℝ), (-2224489131/10000000000 : ℝ)] ![(8720077223803/20000000000000 : ℝ), (42751834222729/100000000000000 : ℝ), (13647779654077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668086891/1250000000 : ℝ)|^8349 ≤ (8720077223803/20000000000000 : ℝ)^6301
        have hw : |(668086891/1250000000 : ℝ)|=(668086891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266003251/10000000000 : ℝ)|^8349 ≤ (42751834222729/100000000000000 : ℝ)^6301
        have hw : |(5266003251/10000000000 : ℝ)|=(5266003251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2224489131/10000000000 : ℝ)|^8349 ≤ (13647779654077/100000000000000 : ℝ)^6301
        have hw : |(-2224489131/10000000000 : ℝ)|=(2224489131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362706593/10000000000 : ℝ)*x 0 + (2119053991/5000000000 : ℝ)*x 1 + (1122734621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362706593/10000000000 : ℝ)^8349 ≤ (33317062458567/100000000000000 : ℝ)^6301 := by
    have hnat : (4362706593 : ℕ)^8349*100000000000000^6301 ≤ 33317062458567^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362706593 10000000000 33317062458567 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119053991/5000000000 : ℝ)^8349 ≤ (32062144635731/100000000000000 : ℝ)^6301 := by
    have hnat : (2119053991 : ℕ)^8349*100000000000000^6301 ≤ 32062144635731^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119053991 5000000000 32062144635731 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122734621/2500000000 : ℝ)^8349 ≤ (34620792894097/100000000000000 : ℝ)^6301 := by
    have hnat : (1122734621 : ℕ)^8349*100000000000000^6301 ≤ 34620792894097^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122734621 2500000000 34620792894097 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362706593/10000000000 : ℝ), (2119053991/5000000000 : ℝ), (1122734621/2500000000 : ℝ)] ![(33317062458567/100000000000000 : ℝ), (32062144635731/100000000000000 : ℝ), (34620792894097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362706593/10000000000 : ℝ)|^8349 ≤ (33317062458567/100000000000000 : ℝ)^6301
        have hw : |(4362706593/10000000000 : ℝ)|=(4362706593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119053991/5000000000 : ℝ)|^8349 ≤ (32062144635731/100000000000000 : ℝ)^6301
        have hw : |(2119053991/5000000000 : ℝ)|=(2119053991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122734621/2500000000 : ℝ)|^8349 ≤ (34620792894097/100000000000000 : ℝ)^6301
        have hw : |(1122734621/2500000000 : ℝ)|=(1122734621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160216127/10000000000 : ℝ)*x 0 + (658290263/1250000000 : ℝ)*x 1 + (1348104673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160216127/10000000000 : ℝ)^8349 ≤ (6563875217813/50000000000000 : ℝ)^6301 := by
    have hnat : (2160216127 : ℕ)^8349*50000000000000^6301 ≤ 6563875217813^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160216127 10000000000 6563875217813 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658290263/1250000000 : ℝ)^8349 ≤ (21377632108489/50000000000000 : ℝ)^6301 := by
    have hnat : (658290263 : ℕ)^8349*50000000000000^6301 ≤ 21377632108489^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658290263 1250000000 21377632108489 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348104673/2500000000 : ℝ)^8349 ≤ (44116985333807/100000000000000 : ℝ)^6301 := by
    have hnat : (1348104673 : ℕ)^8349*100000000000000^6301 ≤ 44116985333807^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348104673 2500000000 44116985333807 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160216127/10000000000 : ℝ), (658290263/1250000000 : ℝ), (1348104673/2500000000 : ℝ)] ![(6563875217813/50000000000000 : ℝ), (21377632108489/50000000000000 : ℝ), (44116985333807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160216127/10000000000 : ℝ)|^8349 ≤ (6563875217813/50000000000000 : ℝ)^6301
        have hw : |(-2160216127/10000000000 : ℝ)|=(2160216127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658290263/1250000000 : ℝ)|^8349 ≤ (21377632108489/50000000000000 : ℝ)^6301
        have hw : |(658290263/1250000000 : ℝ)|=(658290263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348104673/2500000000 : ℝ)|^8349 ≤ (44116985333807/100000000000000 : ℝ)^6301
        have hw : |(1348104673/2500000000 : ℝ)|=(1348104673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312552929/10000000000 : ℝ)*x 0 + (-1049036137/5000000000 : ℝ)*x 1 + (269620993/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312552929/10000000000 : ℝ)^8349 ≤ (21626647808169/50000000000000 : ℝ)^6301 := by
    have hnat : (5312552929 : ℕ)^8349*50000000000000^6301 ≤ 21626647808169^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312552929 10000000000 21626647808169 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049036137/5000000000 : ℝ)^8349 ≤ (2525941274489/20000000000000 : ℝ)^6301 := by
    have hnat : (1049036137 : ℕ)^8349*20000000000000^6301 ≤ 2525941274489^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049036137 5000000000 2525941274489 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269620993/500000000 : ℝ)^8349 ≤ (882339959909/2000000000000 : ℝ)^6301 := by
    have hnat : (269620993 : ℕ)^8349*2000000000000^6301 ≤ 882339959909^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269620993 500000000 882339959909 2000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312552929/10000000000 : ℝ), (-1049036137/5000000000 : ℝ), (269620993/500000000 : ℝ)] ![(21626647808169/50000000000000 : ℝ), (2525941274489/20000000000000 : ℝ), (882339959909/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312552929/10000000000 : ℝ)|^8349 ≤ (21626647808169/50000000000000 : ℝ)^6301
        have hw : |(5312552929/10000000000 : ℝ)|=(5312552929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049036137/5000000000 : ℝ)|^8349 ≤ (2525941274489/20000000000000 : ℝ)^6301
        have hw : |(-1049036137/5000000000 : ℝ)|=(1049036137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269620993/500000000 : ℝ)|^8349 ≤ (882339959909/2000000000000 : ℝ)^6301
        have hw : |(269620993/500000000 : ℝ)|=(269620993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312553327/10000000000 : ℝ)*x 0 + (2696209639/5000000000 : ℝ)*x 1 + (-2098072527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312553327/10000000000 : ℝ)^8349 ≤ (21626649954981/50000000000000 : ℝ)^6301 := by
    have hnat : (5312553327 : ℕ)^8349*50000000000000^6301 ≤ 21626649954981^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312553327 10000000000 21626649954981 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696209639/5000000000 : ℝ)^8349 ≤ (44116991686309/100000000000000 : ℝ)^6301 := by
    have hnat : (2696209639 : ℕ)^8349*100000000000000^6301 ≤ 44116991686309^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696209639 5000000000 44116991686309 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098072527/10000000000 : ℝ)^8349 ≤ (12629708390431/100000000000000 : ℝ)^6301 := by
    have hnat : (2098072527 : ℕ)^8349*100000000000000^6301 ≤ 12629708390431^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098072527 10000000000 12629708390431 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312553327/10000000000 : ℝ), (2696209639/5000000000 : ℝ), (-2098072527/10000000000 : ℝ)] ![(21626649954981/50000000000000 : ℝ), (44116991686309/100000000000000 : ℝ), (12629708390431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312553327/10000000000 : ℝ)|^8349 ≤ (21626649954981/50000000000000 : ℝ)^6301
        have hw : |(5312553327/10000000000 : ℝ)|=(5312553327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696209639/5000000000 : ℝ)|^8349 ≤ (44116991686309/100000000000000 : ℝ)^6301
        have hw : |(2696209639/5000000000 : ℝ)|=(2696209639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098072527/10000000000 : ℝ)|^8349 ≤ (12629708390431/100000000000000 : ℝ)^6301
        have hw : |(-2098072527/10000000000 : ℝ)|=(2098072527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s8_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136334869/312500000 : ℝ)*x 0 + (4490303797/10000000000 : ℝ)*x 1 + (4238745403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136334869/312500000 : ℝ)^8349 ≤ (8329288926193/25000000000000 : ℝ)^6301 := by
    have hnat : (136334869 : ℕ)^8349*25000000000000^6301 ≤ 8329288926193^6301*312500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136334869 312500000 8329288926193 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490303797/10000000000 : ℝ)^8349 ≤ (6922861983323/20000000000000 : ℝ)^6301 := by
    have hnat : (4490303797 : ℕ)^8349*20000000000000^6301 ≤ 6922861983323^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490303797 10000000000 6922861983323 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238745403/10000000000 : ℝ)^8349 ≤ (16034267182919/50000000000000 : ℝ)^6301 := by
    have hnat : (4238745403 : ℕ)^8349*50000000000000^6301 ≤ 16034267182919^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238745403 10000000000 16034267182919 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136334869/312500000 : ℝ), (4490303797/10000000000 : ℝ), (4238745403/10000000000 : ℝ)] ![(8329288926193/25000000000000 : ℝ), (6922861983323/20000000000000 : ℝ), (16034267182919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136334869/312500000 : ℝ)|^8349 ≤ (8329288926193/25000000000000 : ℝ)^6301
        have hw : |(136334869/312500000 : ℝ)|=(136334869/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490303797/10000000000 : ℝ)|^8349 ≤ (6922861983323/20000000000000 : ℝ)^6301
        have hw : |(4490303797/10000000000 : ℝ)|=(4490303797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238745403/10000000000 : ℝ)|^8349 ≤ (16034267182919/50000000000000 : ℝ)^6301
        have hw : |(4238745403/10000000000 : ℝ)|=(4238745403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2843/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11371/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (1770855255377177/12500000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^2087 ≤ (1770855255377177/12500000000000000000 : ℝ)^512 := by
      have hnat : (11371 : ℕ)^2087*12500000000000000000^512 ≤ 1770855255377177^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 1770855255377177 12500000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (1770855255377177/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (2087/512 : ℝ) ≤ (33634880903412027/100000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^2087 ≤ (33634880903412027/100000000000000000000 : ℝ)^512 := by
      have hnat : (7029 : ℕ)^2087*100000000000000000000^512 ≤ 33634880903412027^512*50000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 33634880903412027 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (33634880903412027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251770855255377177/6250000000000000000 : ℝ) ≤ (10000695030931303/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (6251770855255377177/6250000000000000000 : ℝ)^512 ≤ (10000695030931303/10000000000000000 : ℝ)^2087 := by
      have hnat : (6251770855255377177 : ℕ)^512*10000000000000000^2087 ≤ 10000695030931303^2087*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251770855255377177 6250000000000000000 10000695030931303 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000695030931303/10000000000000000 : ℝ)) (X := (6251770855255377177/6250000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047801722946429443/100000000000000000000 : ℝ) ≤ (10001172499705093/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100047801722946429443/100000000000000000000 : ℝ)^512 ≤ (10001172499705093/10000000000000000 : ℝ)^2087 := by
      have hnat : (100047801722946429443 : ℕ)^512*10000000000000000^2087 ≤ 10001172499705093^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047801722946429443 100000000000000000000 10001172499705093 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001172499705093/10000000000000000 : ℝ)) (X := (100047801722946429443/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033634880903412027/50000000000000000000 : ℝ) ≤ (10001649968478883/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50033634880903412027/50000000000000000000 : ℝ)^512 ≤ (10001649968478883/10000000000000000 : ℝ)^2087 := by
      have hnat : (50033634880903412027 : ℕ)^512*10000000000000000^2087 ≤ 10001649968478883^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033634880903412027 50000000000000000000 10001649968478883 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001649968478883/10000000000000000 : ℝ)) (X := (50033634880903412027/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1770855255377177/12500000000000000000 : ℝ) ≤ ((26861008953258878981/26870000000000000000 : ℝ)+2*(47746877379/26870000000000 : ℝ)*(11371/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (26861008953258878981/26870000000000000000 : ℝ)+2*(47746877379/26870000000000 : ℝ)*(11371/100000 : ℝ)=(10000695030931303/10000000000000000 : ℝ) by norm_num, show 1+2*(1770855255377177/12500000000000000000 : ℝ)=(6251770855255377177/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33634880903412027/100000000000000000000 : ℝ)+(1770855255377177/12500000000000000000 : ℝ) ≤ ((26861008953258878981/26870000000000000000 : ℝ)+(47746877379/26870000000000 : ℝ)*((7029/50000 : ℝ)+(11371/100000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (26861008953258878981/26870000000000000000 : ℝ)+(47746877379/26870000000000 : ℝ)*((7029/50000 : ℝ)+(11371/100000 : ℝ))=(10001172499705093/10000000000000000 : ℝ) by norm_num, show 1+(33634880903412027/100000000000000000000 : ℝ)+(1770855255377177/12500000000000000000 : ℝ)=(100047801722946429443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33634880903412027/100000000000000000000 : ℝ) ≤ ((26861008953258878981/26870000000000000000 : ℝ)+2*(47746877379/26870000000000 : ℝ)*(7029/50000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (26861008953258878981/26870000000000000000 : ℝ)+2*(47746877379/26870000000000 : ℝ)*(7029/50000 : ℝ)=(10001649968478883/10000000000000000 : ℝ) by norm_num, show 1+2*(33634880903412027/100000000000000000000 : ℝ)=(50033634880903412027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26861008953258878981/26870000000000000000 : ℝ)*(X 1 0+X 2 0)+(47746877379/26870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (26861008953258878981/26870000000000000000 : ℝ)) (alpha := (47746877379/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26861008953258878981/26870000000000000000 : ℝ)*(X 0 1+X 2 1)+(47746877379/26870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (26861008953258878981/26870000000000000000 : ℝ)) (alpha := (47746877379/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26861008953258878981/26870000000000000000 : ℝ)*(X 0 2+X 1 2)+(47746877379/26870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (26861008953258878981/26870000000000000000 : ℝ)) (alpha := (47746877379/26870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216021053/1000000000 : ℝ)*X 0 0+(2696369623/5000000000 : ℝ)*X 0 1+(2633001629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344695137/10000000000 : ℝ)*X 1 0+(-1112244553/5000000000 : ℝ)*X 1 1+(263300163/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668086891/1250000000 : ℝ)*X 2 0+(5266003251/10000000000 : ℝ)*X 2 1+(-2224489131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362706593/10000000000 : ℝ)*X 0 0+(2119053991/5000000000 : ℝ)*X 0 1+(1122734621/2500000000 : ℝ)*X 0 2+(4362706593/10000000000 : ℝ)*X 1 0+(2119053991/5000000000 : ℝ)*X 1 1+(1122734621/2500000000 : ℝ)*X 1 2+(4362706593/10000000000 : ℝ)*X 2 0+(2119053991/5000000000 : ℝ)*X 2 1+(1122734621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160216127/10000000000 : ℝ)*X 0 0+(658290263/1250000000 : ℝ)*X 0 1+(1348104673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312552929/10000000000 : ℝ)*X 1 0+(-1049036137/5000000000 : ℝ)*X 1 1+(269620993/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312553327/10000000000 : ℝ)*X 2 0+(2696209639/5000000000 : ℝ)*X 2 1+(-2098072527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136334869/312500000 : ℝ)*X 0 0+(4490303797/10000000000 : ℝ)*X 0 1+(4238745403/10000000000 : ℝ)*X 0 2+(136334869/312500000 : ℝ)*X 1 0+(4490303797/10000000000 : ℝ)*X 1 1+(4238745403/10000000000 : ℝ)*X 1 2+(136334869/312500000 : ℝ)*X 2 0+(4490303797/10000000000 : ℝ)*X 2 1+(4238745403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (527853904963009019622412137/83968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1252280063/100000000000000 : ℝ)*(base19) + (1145607879/100000000000000 : ℝ)*(base23) + (49911593/100000000000000 : ℝ)*(lower2) + (168166439/100000000000000 : ℝ)*(upper3) + (2287389/4000000000000 : ℝ)*(upper5) + (740359041953691/12500000000000 : ℝ)*(major0) + (740359041953691/12500000000000 : ℝ)*(major1) + (740359041953691/12500000000000 : ℝ)*(major2) + (1578091276603497/20000000000000 : ℝ)*(sp0) + (789048884818943/10000000000000 : ℝ)*(sp1) + (3945244477430807/50000000000000 : ℝ)*(sp2) + (3955235286767047/100000000000000 : ℝ)*(sp3) + (4214681501/12500000000000 : ℝ)*(sp4) + (19074478713/100000000000000 : ℝ)*(sp7) + (12360169878893/312500000000 : ℝ)*(f.failure) + (7890490100469493/100000000000000 : ℝ)*(f.sum) + (7488916643259/2687000000000000000000000000 : ℝ)*base66 + (3447076781956893871/335875000000000000000000000000000 : ℝ)*base67 + (9143080414500393871/335875000000000000000000000000000 : ℝ)*base69 + (2024392237960106129/335875000000000000000000000000000 : ℝ)*base72 + (1900243953421/2687000000000000000000000000 : ℝ)*base74 + (10135778412743143871/335875000000000000000000000000000 : ℝ)*base75 + (7217472155723143871/335875000000000000000000000000000 : ℝ)*base77 + (6125409201111393871/335875000000000000000000000000000 : ℝ)*base79 + (1706330735387/2687000000000000000000000000 : ℝ)*base82 + (41473/31250000000000000000 : ℝ)*base90 + (41473/31250000000000000000 : ℝ)*base92 + (41473/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3216380168991067794873/671750000000000000000000000 : ℝ) := by norm_num
    linear_combination (141101221/6250000000000 : ℝ)*(base19) + (2272651343/50000000000000 : ℝ)*(base23) + (682349151/50000000000000 : ℝ)*(lower1) + (92036677/12500000000000 : ℝ)*(upper2) + (300887157/50000000000000 : ℝ)*(upper3) + (1488184376470461/25000000000000 : ℝ)*(major0) + (1488184376470461/25000000000000 : ℝ)*(major1) + (1488184376470461/25000000000000 : ℝ)*(major2) + (2542258539/5000000000000 : ℝ)*(sp2) + (1417255217/12500000000000 : ℝ)*(sp3) + (1982569182707131/25000000000000 : ℝ)*(sp4) + (1982568618302247/25000000000000 : ℝ)*(sp5) + (3965110670177529/50000000000000 : ℝ)*(sp6) + (1987593391645689/50000000000000 : ℝ)*(sp7) + (1987599060666557/50000000000000 : ℝ)*(f.failure) + (1982569182707131/25000000000000 : ℝ)*(f.sum) + (1984697212709/671750000000000000000000000 : ℝ)*base66 + (2935622885009780241/671750000000000000000000000000000 : ℝ)*base67 + (322082917971219759/671750000000000000000000000000000 : ℝ)*base70 + (1858926377807719759/671750000000000000000000000000000 : ℝ)*base72 + (270055429153/268700000000000000000000000 : ℝ)*base73 + (109629934412780241/671750000000000000000000000000000 : ℝ)*base75 + (23156499457907219759/671750000000000000000000000000000 : ℝ)*base78 + (12958590072685780241/671750000000000000000000000000000 : ℝ)*base79 + (2476994230273/671750000000000000000000000 : ℝ)*base82 + (10419023/5000000000000000000000 : ℝ)*base89 + (10419023/5000000000000000000000 : ℝ)*base91 + (10419023/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1156_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1156_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1156_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1156_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
