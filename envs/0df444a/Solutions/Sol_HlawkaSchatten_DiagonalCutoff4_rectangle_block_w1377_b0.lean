-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:09.94047+00:00
-- url     : https://prove2.me/submissions/59539441-4428-4e9d-bea4-d35b6efb4def

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
theorem support_rectangle_w1377_s0_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71545393/400000000 : ℝ)*x 0 + (1495484267/2500000000 : ℝ)*x 1 + (963838149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71545393/400000000 : ℝ)^4337 ≤ (5253600396349/50000000000000 : ℝ)^3313 := by
    have hnat : (71545393 : ℕ)^4337*50000000000000^3313 ≤ 5253600396349^3313*400000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71545393 400000000 5253600396349 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1495484267/2500000000 : ℝ)^4337 ≤ (25517428715629/50000000000000 : ℝ)^3313 := by
    have hnat : (1495484267 : ℕ)^4337*50000000000000^3313 ≤ 25517428715629^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495484267 2500000000 25517428715629 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963838149/2000000000 : ℝ)^4337 ≤ (150226334977/390625000000 : ℝ)^3313 := by
    have hnat : (963838149 : ℕ)^4337*390625000000^3313 ≤ 150226334977^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963838149 2000000000 150226334977 390625000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71545393/400000000 : ℝ), (1495484267/2500000000 : ℝ), (963838149/2000000000 : ℝ)] ![(5253600396349/50000000000000 : ℝ), (25517428715629/50000000000000 : ℝ), (150226334977/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71545393/400000000 : ℝ)|^4337 ≤ (5253600396349/50000000000000 : ℝ)^3313
        have hw : |(-71545393/400000000 : ℝ)|=(71545393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1495484267/2500000000 : ℝ)|^4337 ≤ (25517428715629/50000000000000 : ℝ)^3313
        have hw : |(1495484267/2500000000 : ℝ)|=(1495484267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963838149/2000000000 : ℝ)|^4337 ≤ (150226334977/390625000000 : ℝ)^3313
        have hw : |(963838149/2000000000 : ℝ)|=(963838149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2748948721/5000000000 : ℝ)*x 0 + (-2447871089/10000000000 : ℝ)*x 1 + (4819191381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748948721/5000000000 : ℝ)^4337 ≤ (22848895208297/50000000000000 : ℝ)^3313 := by
    have hnat : (2748948721 : ℕ)^4337*50000000000000^3313 ≤ 22848895208297^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748948721 5000000000 22848895208297 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2447871089/10000000000 : ℝ)^4337 ≤ (79221305849/500000000000 : ℝ)^3313 := by
    have hnat : (2447871089 : ℕ)^4337*500000000000^3313 ≤ 79221305849^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447871089 10000000000 79221305849 500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819191381/10000000000 : ℝ)^4337 ≤ (19228974199113/50000000000000 : ℝ)^3313 := by
    have hnat : (4819191381 : ℕ)^4337*50000000000000^3313 ≤ 19228974199113^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819191381 10000000000 19228974199113 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748948721/5000000000 : ℝ), (-2447871089/10000000000 : ℝ), (4819191381/10000000000 : ℝ)] ![(22848895208297/50000000000000 : ℝ), (79221305849/500000000000 : ℝ), (19228974199113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748948721/5000000000 : ℝ)|^4337 ≤ (22848895208297/50000000000000 : ℝ)^3313
        have hw : |(2748948721/5000000000 : ℝ)|=(2748948721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2447871089/10000000000 : ℝ)|^4337 ≤ (79221305849/500000000000 : ℝ)^3313
        have hw : |(-2447871089/10000000000 : ℝ)|=(2447871089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819191381/10000000000 : ℝ)|^4337 ≤ (19228974199113/50000000000000 : ℝ)^3313
        have hw : |(4819191381/10000000000 : ℝ)|=(4819191381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2748948661/5000000000 : ℝ)*x 0 + (4819190649/10000000000 : ℝ)*x 1 + (-489574429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748948661/5000000000 : ℝ)^4337 ≤ (285611181943/625000000000 : ℝ)^3313 := by
    have hnat : (2748948661 : ℕ)^4337*625000000000^3313 ≤ 285611181943^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748948661 5000000000 285611181943 625000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819190649/10000000000 : ℝ)^4337 ≤ (38457940751227/100000000000000 : ℝ)^3313 := by
    have hnat : (4819190649 : ℕ)^4337*100000000000000^3313 ≤ 38457940751227^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819190649 10000000000 38457940751227 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489574429/2000000000 : ℝ)^4337 ≤ (7922135058791/50000000000000 : ℝ)^3313 := by
    have hnat : (489574429 : ℕ)^4337*50000000000000^3313 ≤ 7922135058791^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489574429 2000000000 7922135058791 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748948661/5000000000 : ℝ), (4819190649/10000000000 : ℝ), (-489574429/2000000000 : ℝ)] ![(285611181943/625000000000 : ℝ), (38457940751227/100000000000000 : ℝ), (7922135058791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748948661/5000000000 : ℝ)|^4337 ≤ (285611181943/625000000000 : ℝ)^3313
        have hw : |(2748948661/5000000000 : ℝ)|=(2748948661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819190649/10000000000 : ℝ)|^4337 ≤ (38457940751227/100000000000000 : ℝ)^3313
        have hw : |(4819190649/10000000000 : ℝ)|=(4819190649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489574429/2000000000 : ℝ)|^4337 ≤ (7922135058791/50000000000000 : ℝ)^3313
        have hw : |(-489574429/2000000000 : ℝ)|=(489574429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086777067/5000000000 : ℝ)*x 0 + (3105012073/10000000000 : ℝ)*x 1 + (696572169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086777067/5000000000 : ℝ)^4337 ≤ (796434404777/2500000000000 : ℝ)^3313 := by
    have hnat : (2086777067 : ℕ)^4337*2500000000000^3313 ≤ 796434404777^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086777067 5000000000 796434404777 2500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105012073/10000000000 : ℝ)^4337 ≤ (4326109002433/20000000000000 : ℝ)^3313 := by
    have hnat : (3105012073 : ℕ)^4337*20000000000000^3313 ≤ 4326109002433^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105012073 10000000000 4326109002433 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696572169/1250000000 : ℝ)^4337 ≤ (9302415756153/20000000000000 : ℝ)^3313 := by
    have hnat : (696572169 : ℕ)^4337*20000000000000^3313 ≤ 9302415756153^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696572169 1250000000 9302415756153 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086777067/5000000000 : ℝ), (3105012073/10000000000 : ℝ), (696572169/1250000000 : ℝ)] ![(796434404777/2500000000000 : ℝ), (4326109002433/20000000000000 : ℝ), (9302415756153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086777067/5000000000 : ℝ)|^4337 ≤ (796434404777/2500000000000 : ℝ)^3313
        have hw : |(2086777067/5000000000 : ℝ)|=(2086777067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105012073/10000000000 : ℝ)|^4337 ≤ (4326109002433/20000000000000 : ℝ)^3313
        have hw : |(3105012073/10000000000 : ℝ)|=(3105012073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(696572169/1250000000 : ℝ)|^4337 ≤ (9302415756153/20000000000000 : ℝ)^3313
        have hw : |(696572169/1250000000 : ℝ)|=(696572169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448227811/2500000000 : ℝ)*x 0 + (2424525599/5000000000 : ℝ)*x 1 + (297550459/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448227811/2500000000 : ℝ)^4337 ≤ (10540099129113/100000000000000 : ℝ)^3313 := by
    have hnat : (448227811 : ℕ)^4337*100000000000000^3313 ≤ 10540099129113^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448227811 2500000000 10540099129113 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424525599/5000000000 : ℝ)^4337 ≤ (38770183794839/100000000000000 : ℝ)^3313 := by
    have hnat : (2424525599 : ℕ)^4337*100000000000000^3313 ≤ 38770183794839^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424525599 5000000000 38770183794839 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297550459/500000000 : ℝ)^4337 ≤ (10137943413297/20000000000000 : ℝ)^3313 := by
    have hnat : (297550459 : ℕ)^4337*20000000000000^3313 ≤ 10137943413297^3313*500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297550459 500000000 10137943413297 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448227811/2500000000 : ℝ), (2424525599/5000000000 : ℝ), (297550459/500000000 : ℝ)] ![(10540099129113/100000000000000 : ℝ), (38770183794839/100000000000000 : ℝ), (10137943413297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448227811/2500000000 : ℝ)|^4337 ≤ (10540099129113/100000000000000 : ℝ)^3313
        have hw : |(-448227811/2500000000 : ℝ)|=(448227811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424525599/5000000000 : ℝ)|^4337 ≤ (38770183794839/100000000000000 : ℝ)^3313
        have hw : |(2424525599/5000000000 : ℝ)|=(2424525599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297550459/500000000 : ℝ)|^4337 ≤ (10137943413297/20000000000000 : ℝ)^3313
        have hw : |(297550459/500000000 : ℝ)|=(297550459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180804053/10000000000 : ℝ)*x 0 + (-263211179/2000000000 : ℝ)*x 1 + (2975503873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180804053/10000000000 : ℝ)^4337 ≤ (21139343666019/50000000000000 : ℝ)^3313 := by
    have hnat : (5180804053 : ℕ)^4337*50000000000000^3313 ≤ 21139343666019^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180804053 10000000000 21139343666019 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263211179/2000000000 : ℝ)^4337 ≤ (140632231311/2000000000000 : ℝ)^3313 := by
    have hnat : (263211179 : ℕ)^4337*2000000000000^3313 ≤ 140632231311^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263211179 2000000000 140632231311 2000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2975503873/5000000000 : ℝ)^4337 ≤ (50689701076563/100000000000000 : ℝ)^3313 := by
    have hnat : (2975503873 : ℕ)^4337*100000000000000^3313 ≤ 50689701076563^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975503873 5000000000 50689701076563 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180804053/10000000000 : ℝ), (-263211179/2000000000 : ℝ), (2975503873/5000000000 : ℝ)] ![(21139343666019/50000000000000 : ℝ), (140632231311/2000000000000 : ℝ), (50689701076563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180804053/10000000000 : ℝ)|^4337 ≤ (21139343666019/50000000000000 : ℝ)^3313
        have hw : |(5180804053/10000000000 : ℝ)|=(5180804053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263211179/2000000000 : ℝ)|^4337 ≤ (140632231311/2000000000000 : ℝ)^3313
        have hw : |(-263211179/2000000000 : ℝ)|=(263211179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2975503873/5000000000 : ℝ)|^4337 ≤ (50689701076563/100000000000000 : ℝ)^3313
        have hw : |(2975503873/5000000000 : ℝ)|=(2975503873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259040121/500000000 : ℝ)*x 0 + (5951010889/10000000000 : ℝ)*x 1 + (-65802669/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259040121/500000000 : ℝ)^4337 ≤ (42278669886737/100000000000000 : ℝ)^3313 := by
    have hnat : (259040121 : ℕ)^4337*100000000000000^3313 ≤ 42278669886737^3313*500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259040121 500000000 42278669886737 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5951010889/10000000000 : ℝ)^4337 ≤ (25344868061409/50000000000000 : ℝ)^3313 := by
    have hnat : (5951010889 : ℕ)^4337*50000000000000^3313 ≤ 25344868061409^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951010889 10000000000 25344868061409 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65802669/500000000 : ℝ)^4337 ≤ (3515796987359/50000000000000 : ℝ)^3313 := by
    have hnat : (65802669 : ℕ)^4337*50000000000000^3313 ≤ 3515796987359^3313*500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65802669 500000000 3515796987359 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259040121/500000000 : ℝ), (5951010889/10000000000 : ℝ), (-65802669/500000000 : ℝ)] ![(42278669886737/100000000000000 : ℝ), (25344868061409/50000000000000 : ℝ), (3515796987359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259040121/500000000 : ℝ)|^4337 ≤ (42278669886737/100000000000000 : ℝ)^3313
        have hw : |(259040121/500000000 : ℝ)|=(259040121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5951010889/10000000000 : ℝ)|^4337 ≤ (25344868061409/50000000000000 : ℝ)^3313
        have hw : |(5951010889/10000000000 : ℝ)|=(5951010889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65802669/500000000 : ℝ)|^4337 ≤ (3515796987359/50000000000000 : ℝ)^3313
        have hw : |(-65802669/500000000 : ℝ)|=(65802669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s0_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182620231/10000000000 : ℝ)*x 0 + (5509211149/10000000000 : ℝ)*x 1 + (3170648887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182620231/10000000000 : ℝ)^4337 ≤ (15973999550129/50000000000000 : ℝ)^3313 := by
    have hnat : (4182620231 : ℕ)^4337*50000000000000^3313 ≤ 15973999550129^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182620231 10000000000 15973999550129 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509211149/10000000000 : ℝ)^4337 ≤ (45820933353921/100000000000000 : ℝ)^3313 := by
    have hnat : (5509211149 : ℕ)^4337*100000000000000^3313 ≤ 45820933353921^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509211149 10000000000 45820933353921 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170648887/10000000000 : ℝ)^4337 ≤ (22231067531217/100000000000000 : ℝ)^3313 := by
    have hnat : (3170648887 : ℕ)^4337*100000000000000^3313 ≤ 22231067531217^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170648887 10000000000 22231067531217 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182620231/10000000000 : ℝ), (5509211149/10000000000 : ℝ), (3170648887/10000000000 : ℝ)] ![(15973999550129/50000000000000 : ℝ), (45820933353921/100000000000000 : ℝ), (22231067531217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182620231/10000000000 : ℝ)|^4337 ≤ (15973999550129/50000000000000 : ℝ)^3313
        have hw : |(4182620231/10000000000 : ℝ)|=(4182620231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509211149/10000000000 : ℝ)|^4337 ≤ (45820933353921/100000000000000 : ℝ)^3313
        have hw : |(5509211149/10000000000 : ℝ)|=(5509211149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170648887/10000000000 : ℝ)|^4337 ≤ (22231067531217/100000000000000 : ℝ)^3313
        have hw : |(3170648887/10000000000 : ℝ)|=(3170648887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (837/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26621/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
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
  have hpowlo : (0 : ℝ) ^ (271/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^271 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^271*1^64 ≤ 0^64*1^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (271/64 : ℝ) ≤ (1032625344636574029/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^271 ≤ (1032625344636574029/50000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^271*50000000000000000000^64 ≤ 1032625344636574029^64*5^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1032625344636574029 50000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1032625344636574029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^271 := by
      have hnat : (1 : ℕ)^64*1^271 ≤ 1^271*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (51032625344636574029/50000000000000000000 : ℝ) ≤ (10048393349144643/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (51032625344636574029/50000000000000000000 : ℝ)^64 ≤ (10048393349144643/10000000000000000 : ℝ)^271 := by
      have hnat : (51032625344636574029 : ℕ)^64*10000000000000000^271 ≤ 10048393349144643^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51032625344636574029 50000000000000000000 10048393349144643 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048393349144643/10000000000000000 : ℝ)) (X := (51032625344636574029/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (26032625344636574029/25000000000000000000 : ℝ) ≤ (5048393349144643/5000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (26032625344636574029/25000000000000000000 : ℝ)^64 ≤ (5048393349144643/5000000000000000 : ℝ)^271 := by
      have hnat : (26032625344636574029 : ℕ)^64*5000000000000000^271 ≤ 5048393349144643^271*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26032625344636574029 25000000000000000000 5048393349144643 5000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048393349144643/5000000000000000 : ℝ)) (X := (26032625344636574029/25000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48393349144643/4000000000000000 : ℝ)*(0 : ℝ))^(271/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(48393349144643/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1032625344636574029/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48393349144643/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(271/64 : ℝ) := by
    rw [show (1 : ℝ)+(48393349144643/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048393349144643/10000000000000000 : ℝ) by norm_num, show 1+(1032625344636574029/50000000000000000000 : ℝ)+(0 : ℝ)=(51032625344636574029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1032625344636574029/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48393349144643/4000000000000000 : ℝ)*(2/5 : ℝ))^(271/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(48393349144643/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048393349144643/5000000000000000 : ℝ) by norm_num, show 1+2*(1032625344636574029/50000000000000000000 : ℝ)=(26032625344636574029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48393349144643/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48393349144643/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48393349144643/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48393349144643/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48393349144643/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48393349144643/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-71545393/400000000 : ℝ)*X 0 0+(1495484267/2500000000 : ℝ)*X 0 1+(963838149/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2748948721/5000000000 : ℝ)*X 1 0+(-2447871089/10000000000 : ℝ)*X 1 1+(4819191381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748948661/5000000000 : ℝ)*X 2 0+(4819190649/10000000000 : ℝ)*X 2 1+(-489574429/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2086777067/5000000000 : ℝ)*X 0 0+(3105012073/10000000000 : ℝ)*X 0 1+(696572169/1250000000 : ℝ)*X 0 2+(2086777067/5000000000 : ℝ)*X 1 0+(3105012073/10000000000 : ℝ)*X 1 1+(696572169/1250000000 : ℝ)*X 1 2+(2086777067/5000000000 : ℝ)*X 2 0+(3105012073/10000000000 : ℝ)*X 2 1+(696572169/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-448227811/2500000000 : ℝ)*X 0 0+(2424525599/5000000000 : ℝ)*X 0 1+(297550459/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180804053/10000000000 : ℝ)*X 1 0+(-263211179/2000000000 : ℝ)*X 1 1+(2975503873/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259040121/500000000 : ℝ)*X 2 0+(5951010889/10000000000 : ℝ)*X 2 1+(-65802669/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4182620231/10000000000 : ℝ)*X 0 0+(5509211149/10000000000 : ℝ)*X 0 1+(3170648887/10000000000 : ℝ)*X 0 2+(4182620231/10000000000 : ℝ)*X 1 0+(5509211149/10000000000 : ℝ)*X 1 1+(3170648887/10000000000 : ℝ)*X 1 2+(4182620231/10000000000 : ℝ)*X 2 0+(5509211149/10000000000 : ℝ)*X 2 1+(3170648887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146949689995467616228833/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1583689/781250000000 : ℝ)*(base1) + (56798553/100000000000000 : ℝ)*(base16) + (312910409/50000000000000 : ℝ)*(base19) + (331923893/50000000000000 : ℝ)*(base23) + (22707277/25000000000000 : ℝ)*(upper3) + (632647703045223/100000000000000 : ℝ)*(major0) + (632647703045223/100000000000000 : ℝ)*(major1) + (632647703045223/100000000000000 : ℝ)*(major2) + (430017415236501/50000000000000 : ℝ)*(sp0) + (107504423197833/12500000000000 : ℝ)*(sp1) + (860035404354249/100000000000000 : ℝ)*(sp2) + (20262913874099/5000000000000 : ℝ)*(sp3) + (57617649/4000000000000 : ℝ)*(sp4) + (94965971/12500000000000 : ℝ)*(sp7) + (20262961996097/5000000000000 : ℝ)*(f.failure) + (215009017050509/25000000000000 : ℝ)*(f.sum) + (300003161590389/200000000000000000000000000000 : ℝ)*base65 + (2308211133990389/400000000000000000000000000000 : ℝ)*base67 + (2379324130790389/400000000000000000000000000000 : ℝ)*base69 + (3375563310790389/400000000000000000000000000000 : ℝ)*base71 + (295912378009611/200000000000000000000000000000 : ℝ)*base74 + (3349081333190389/400000000000000000000000000000 : ℝ)*base75 + (3123053034790389/400000000000000000000000000000 : ℝ)*base77 + (3791274367990389/400000000000000000000000000000 : ℝ)*base79 + (395369982990389/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (240719/62500000000000000000 : ℝ)*base90 + (240719/62500000000000000000 : ℝ)*base92 + (240719/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (716832142651139377382193/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79672847/25000000000000 : ℝ)*(base19) + (124473077/100000000000000 : ℝ)*(base23) + (31873563/50000000000000 : ℝ)*(base39) + (273511/25000000000000 : ℝ)*(base53) + (10725969/10000000000000 : ℝ)*(upper2) + (7320749/5000000000000 : ℝ)*(upper4) + (667544257434509/100000000000000 : ℝ)*(major0) + (667544257434509/100000000000000 : ℝ)*(major1) + (667544193687383/100000000000000 : ℝ)*(major2) + (6710133/390625000000 : ℝ)*(sp2) + (907475179685529/100000000000000 : ℝ)*(sp4) + (907474860994141/100000000000000 : ℝ)*(sp5) + (90747340116553/10000000000000 : ℝ)*(sp6) + (26725821997771/6250000000000 : ℝ)*(sp7) + (26725821997771/6250000000000 : ℝ)*(f.failure) + (181495048686531/20000000000000 : ℝ)*(f.sum) + (208393628956139/100000000000000000000000000000 : ℝ)*base65 + (396304868739269/400000000000000000000000000000 : ℝ)*base67 + (914991360114713/400000000000000000000000000000 : ℝ)*base70 + (2138769155539269/400000000000000000000000000000 : ℝ)*base71 + (41824103943861/100000000000000000000000000000 : ℝ)*base74 + (1581224653485287/400000000000000000000000000000 : ℝ)*base75 + (28547271885287/400000000000000000000000000000 : ℝ)*base77 + (2245710586285287/400000000000000000000000000000 : ℝ)*base79 + (589313193714713/200000000000000000000000000000 : ℝ)*base82 + (133367/78125000000000000000 : ℝ)*base90 + (133367/78125000000000000000 : ℝ)*base92 + (133367/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (837/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_s1_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61512981/312500000 : ℝ)*x 0 + (351673271/625000000 : ℝ)*x 1 + (2529591049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61512981/312500000 : ℝ)^4337 ≤ (2382146831617/20000000000000 : ℝ)^3313 := by
    have hnat : (61512981 : ℕ)^4337*20000000000000^3313 ≤ 2382146831617^3313*312500000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61512981 312500000 2382146831617 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351673271/625000000 : ℝ)^4337 ≤ (47105123595013/100000000000000 : ℝ)^3313 := by
    have hnat : (351673271 : ℕ)^4337*100000000000000^3313 ≤ 47105123595013^3313*625000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351673271 625000000 47105123595013 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529591049/5000000000 : ℝ)^4337 ≤ (40984142224439/100000000000000 : ℝ)^3313 := by
    have hnat : (2529591049 : ℕ)^4337*100000000000000^3313 ≤ 40984142224439^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529591049 5000000000 40984142224439 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61512981/312500000 : ℝ), (351673271/625000000 : ℝ), (2529591049/5000000000 : ℝ)] ![(2382146831617/20000000000000 : ℝ), (47105123595013/100000000000000 : ℝ), (40984142224439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61512981/312500000 : ℝ)|^4337 ≤ (2382146831617/20000000000000 : ℝ)^3313
        have hw : |(-61512981/312500000 : ℝ)|=(61512981/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(351673271/625000000 : ℝ)|^4337 ≤ (47105123595013/100000000000000 : ℝ)^3313
        have hw : |(351673271/625000000 : ℝ)|=(351673271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529591049/5000000000 : ℝ)|^4337 ≤ (40984142224439/100000000000000 : ℝ)^3313
        have hw : |(2529591049/5000000000 : ℝ)|=(2529591049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402089917/10000000000 : ℝ)*x 0 + (-2270408649/10000000000 : ℝ)*x 1 + (5059183493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402089917/10000000000 : ℝ)^4337 ≤ (11164533247971/25000000000000 : ℝ)^3313 := by
    have hnat : (5402089917 : ℕ)^4337*25000000000000^3313 ≤ 11164533247971^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402089917 10000000000 11164533247971 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270408649/10000000000 : ℝ)^4337 ≤ (3589427493347/25000000000000 : ℝ)^3313 := by
    have hnat : (2270408649 : ℕ)^4337*25000000000000^3313 ≤ 3589427493347^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270408649 10000000000 3589427493347 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5059183493/10000000000 : ℝ)^4337 ≤ (40984157018171/100000000000000 : ℝ)^3313 := by
    have hnat : (5059183493 : ℕ)^4337*100000000000000^3313 ≤ 40984157018171^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059183493 10000000000 40984157018171 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402089917/10000000000 : ℝ), (-2270408649/10000000000 : ℝ), (5059183493/10000000000 : ℝ)] ![(11164533247971/25000000000000 : ℝ), (3589427493347/25000000000000 : ℝ), (40984157018171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402089917/10000000000 : ℝ)|^4337 ≤ (11164533247971/25000000000000 : ℝ)^3313
        have hw : |(5402089917/10000000000 : ℝ)|=(5402089917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270408649/10000000000 : ℝ)|^4337 ≤ (3589427493347/25000000000000 : ℝ)^3313
        have hw : |(-2270408649/10000000000 : ℝ)|=(2270408649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5059183493/10000000000 : ℝ)|^4337 ≤ (40984157018171/100000000000000 : ℝ)^3313
        have hw : |(5059183493/10000000000 : ℝ)|=(5059183493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701045259/5000000000 : ℝ)*x 0 + (5059182289/10000000000 : ℝ)*x 1 + (-1135204703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701045259/5000000000 : ℝ)^4337 ≤ (8931627899179/20000000000000 : ℝ)^3313 := by
    have hnat : (2701045259 : ℕ)^4337*20000000000000^3313 ≤ 8931627899179^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701045259 5000000000 8931627899179 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5059182289/10000000000 : ℝ)^4337 ≤ (1024603606249/2500000000000 : ℝ)^3313 := by
    have hnat : (5059182289 : ℕ)^4337*2500000000000^3313 ≤ 1024603606249^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059182289 10000000000 1024603606249 2500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135204703/5000000000 : ℝ)^4337 ≤ (897357265011/6250000000000 : ℝ)^3313 := by
    have hnat : (1135204703 : ℕ)^4337*6250000000000^3313 ≤ 897357265011^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135204703 5000000000 897357265011 6250000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701045259/5000000000 : ℝ), (5059182289/10000000000 : ℝ), (-1135204703/5000000000 : ℝ)] ![(8931627899179/20000000000000 : ℝ), (1024603606249/2500000000000 : ℝ), (897357265011/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701045259/5000000000 : ℝ)|^4337 ≤ (8931627899179/20000000000000 : ℝ)^3313
        have hw : |(2701045259/5000000000 : ℝ)|=(2701045259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5059182289/10000000000 : ℝ)|^4337 ≤ (1024603606249/2500000000000 : ℝ)^3313
        have hw : |(5059182289/10000000000 : ℝ)|=(5059182289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135204703/5000000000 : ℝ)|^4337 ≤ (897357265011/6250000000000 : ℝ)^3313
        have hw : |(-1135204703/5000000000 : ℝ)|=(1135204703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143022153/5000000000 : ℝ)*x 0 + (3722404327/10000000000 : ℝ)*x 1 + (985386467/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143022153/5000000000 : ℝ)^4337 ≤ (32986081888487/100000000000000 : ℝ)^3313 := by
    have hnat : (2143022153 : ℕ)^4337*100000000000000^3313 ≤ 32986081888487^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143022153 5000000000 32986081888487 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3722404327/10000000000 : ℝ)^4337 ≤ (27426561237419/100000000000000 : ℝ)^3313 := by
    have hnat : (3722404327 : ℕ)^4337*100000000000000^3313 ≤ 27426561237419^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722404327 10000000000 27426561237419 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985386467/2000000000 : ℝ)^4337 ≤ (19793678433891/50000000000000 : ℝ)^3313 := by
    have hnat : (985386467 : ℕ)^4337*50000000000000^3313 ≤ 19793678433891^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985386467 2000000000 19793678433891 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143022153/5000000000 : ℝ), (3722404327/10000000000 : ℝ), (985386467/2000000000 : ℝ)] ![(32986081888487/100000000000000 : ℝ), (27426561237419/100000000000000 : ℝ), (19793678433891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143022153/5000000000 : ℝ)|^4337 ≤ (32986081888487/100000000000000 : ℝ)^3313
        have hw : |(2143022153/5000000000 : ℝ)|=(2143022153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3722404327/10000000000 : ℝ)|^4337 ≤ (27426561237419/100000000000000 : ℝ)^3313
        have hw : |(3722404327/10000000000 : ℝ)|=(3722404327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(985386467/2000000000 : ℝ)|^4337 ≤ (19793678433891/50000000000000 : ℝ)^3313
        have hw : |(985386467/2000000000 : ℝ)|=(985386467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246111413/1250000000 : ℝ)*x 0 + (1266528551/2500000000 : ℝ)*x 1 + (5619717569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246111413/1250000000 : ℝ)^4337 ≤ (2382900816507/20000000000000 : ℝ)^3313 := by
    have hnat : (246111413 : ℕ)^4337*20000000000000^3313 ≤ 2382900816507^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246111413 1250000000 2382900816507 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266528551/2500000000 : ℝ)^4337 ≤ (320763059067/781250000000 : ℝ)^3313 := by
    have hnat : (1266528551 : ℕ)^4337*781250000000^3313 ≤ 320763059067^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266528551 2500000000 320763059067 781250000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5619717569/10000000000 : ℝ)^4337 ≤ (47027824344653/100000000000000 : ℝ)^3313 := by
    have hnat : (5619717569 : ℕ)^4337*100000000000000^3313 ≤ 47027824344653^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5619717569 10000000000 47027824344653 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246111413/1250000000 : ℝ), (1266528551/2500000000 : ℝ), (5619717569/10000000000 : ℝ)] ![(2382900816507/20000000000000 : ℝ), (320763059067/781250000000 : ℝ), (47027824344653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246111413/1250000000 : ℝ)|^4337 ≤ (2382900816507/20000000000000 : ℝ)^3313
        have hw : |(-246111413/1250000000 : ℝ)|=(246111413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266528551/2500000000 : ℝ)|^4337 ≤ (320763059067/781250000000 : ℝ)^3313
        have hw : |(1266528551/2500000000 : ℝ)|=(1266528551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5619717569/10000000000 : ℝ)|^4337 ≤ (47027824344653/100000000000000 : ℝ)^3313
        have hw : |(5619717569/10000000000 : ℝ)|=(5619717569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262719327/500000000 : ℝ)*x 0 + (-854937179/5000000000 : ℝ)*x 1 + (561971767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262719327/500000000 : ℝ)^4337 ≤ (43066487187113/100000000000000 : ℝ)^3313 := by
    have hnat : (262719327 : ℕ)^4337*100000000000000^3313 ≤ 43066487187113^3313*500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262719327 500000000 43066487187113 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854937179/5000000000 : ℝ)^4337 ≤ (9905687344439/100000000000000 : ℝ)^3313 := by
    have hnat : (854937179 : ℕ)^4337*100000000000000^3313 ≤ 9905687344439^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854937179 5000000000 9905687344439 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561971767/1000000000 : ℝ)^4337 ≤ (47027825451097/100000000000000 : ℝ)^3313 := by
    have hnat : (561971767 : ℕ)^4337*100000000000000^3313 ≤ 47027825451097^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561971767 1000000000 47027825451097 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262719327/500000000 : ℝ), (-854937179/5000000000 : ℝ), (561971767/1000000000 : ℝ)] ![(43066487187113/100000000000000 : ℝ), (9905687344439/100000000000000 : ℝ), (47027825451097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262719327/500000000 : ℝ)|^4337 ≤ (43066487187113/100000000000000 : ℝ)^3313
        have hw : |(262719327/500000000 : ℝ)|=(262719327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854937179/5000000000 : ℝ)|^4337 ≤ (9905687344439/100000000000000 : ℝ)^3313
        have hw : |(-854937179/5000000000 : ℝ)|=(854937179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561971767/1000000000 : ℝ)|^4337 ≤ (47027825451097/100000000000000 : ℝ)^3313
        have hw : |(561971767/1000000000 : ℝ)|=(561971767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313596609/2500000000 : ℝ)*x 0 + (5619717781/10000000000 : ℝ)*x 1 + (-341974869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313596609/2500000000 : ℝ)^4337 ≤ (4306648607123/10000000000000 : ℝ)^3313 := by
    have hnat : (1313596609 : ℕ)^4337*10000000000000^3313 ≤ 4306648607123^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313596609 2500000000 4306648607123 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5619717781/10000000000 : ℝ)^4337 ≤ (47027826667091/100000000000000 : ℝ)^3313 := by
    have hnat : (5619717781 : ℕ)^4337*100000000000000^3313 ≤ 47027826667091^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5619717781 10000000000 47027826667091 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341974869/2000000000 : ℝ)^4337 ≤ (9905687245849/100000000000000 : ℝ)^3313 := by
    have hnat : (341974869 : ℕ)^4337*100000000000000^3313 ≤ 9905687245849^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341974869 2000000000 9905687245849 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313596609/2500000000 : ℝ), (5619717781/10000000000 : ℝ), (-341974869/2000000000 : ℝ)] ![(4306648607123/10000000000000 : ℝ), (47027826667091/100000000000000 : ℝ), (9905687245849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313596609/2500000000 : ℝ)|^4337 ≤ (4306648607123/10000000000000 : ℝ)^3313
        have hw : |(1313596609/2500000000 : ℝ)|=(1313596609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5619717781/10000000000 : ℝ)|^4337 ≤ (47027826667091/100000000000000 : ℝ)^3313
        have hw : |(5619717781/10000000000 : ℝ)|=(5619717781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341974869/2000000000 : ℝ)|^4337 ≤ (9905687245849/100000000000000 : ℝ)^3313
        have hw : |(-341974869/2000000000 : ℝ)|=(341974869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s1_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143527507/5000000000 : ℝ)*x 0 + (4912223029/10000000000 : ℝ)*x 1 + (747474519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143527507/5000000000 : ℝ)^4337 ≤ (32996265072511/100000000000000 : ℝ)^3313 := by
    have hnat : (2143527507 : ℕ)^4337*100000000000000^3313 ≤ 32996265072511^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143527507 5000000000 32996265072511 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4912223029/10000000000 : ℝ)^4337 ≤ (19716355287079/50000000000000 : ℝ)^3313 := by
    have hnat : (4912223029 : ℕ)^4337*50000000000000^3313 ≤ 19716355287079^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4912223029 10000000000 19716355287079 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (747474519/2000000000 : ℝ)^4337 ≤ (27571024328849/100000000000000 : ℝ)^3313 := by
    have hnat : (747474519 : ℕ)^4337*100000000000000^3313 ≤ 27571024328849^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747474519 2000000000 27571024328849 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143527507/5000000000 : ℝ), (4912223029/10000000000 : ℝ), (747474519/2000000000 : ℝ)] ![(32996265072511/100000000000000 : ℝ), (19716355287079/50000000000000 : ℝ), (27571024328849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143527507/5000000000 : ℝ)|^4337 ≤ (32996265072511/100000000000000 : ℝ)^3313
        have hw : |(2143527507/5000000000 : ℝ)|=(2143527507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4912223029/10000000000 : ℝ)|^4337 ≤ (19716355287079/50000000000000 : ℝ)^3313
        have hw : |(4912223029/10000000000 : ℝ)|=(4912223029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(747474519/2000000000 : ℝ)|^4337 ≤ (27571024328849/100000000000000 : ℝ)^3313
        have hw : |(747474519/2000000000 : ℝ)|=(747474519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (901/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3841/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (837/50000 : ℝ) ^ (271/64 : ℝ) ≤ (3011025954577/100000000000000000000 : ℝ) := by
    have hpowers : (837/50000 : ℝ)^271 ≤ (3011025954577/100000000000000000000 : ℝ)^64 := by
      have hnat : (837 : ℕ)^271*100000000000000000000^64 ≤ 3011025954577^64*50000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        837 50000 3011025954577 100000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (837/50000 : ℝ)) (X := (3011025954577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (26621/100000 : ℝ) ^ (271/64 : ℝ) ≤ (92071333031987227/25000000000000000000 : ℝ) := by
    have hpowers : (26621/100000 : ℝ)^271 ≤ (92071333031987227/25000000000000000000 : ℝ)^64 := by
      have hnat : (26621 : ℕ)^271*25000000000000000000^64 ≤ 92071333031987227^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26621 100000 92071333031987227 25000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26621/100000 : ℝ)) (X := (92071333031987227/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003011025954577/50000000000000000000 : ℝ) ≤ (10000000142218197/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50000003011025954577/50000000000000000000 : ℝ)^64 ≤ (10000000142218197/10000000000000000 : ℝ)^271 := by
      have hnat : (50000003011025954577 : ℕ)^64*10000000000000000^271 ≤ 10000000142218197^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003011025954577 50000000000000000000 10000000142218197 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000142218197/10000000000000000 : ℝ)) (X := (50000003011025954577/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20073657668630780697/20000000000000000000 : ℝ) ≤ (10008685377214503/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (20073657668630780697/20000000000000000000 : ℝ)^64 ≤ (10008685377214503/10000000000000000 : ℝ)^271 := by
      have hnat : (20073657668630780697 : ℕ)^64*10000000000000000^271 ≤ 10008685377214503^271*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20073657668630780697 20000000000000000000 10008685377214503 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008685377214503/10000000000000000 : ℝ)) (X := (20073657668630780697/20000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12592071333031987227/12500000000000000000 : ℝ) ≤ (10017370612210809/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (12592071333031987227/12500000000000000000 : ℝ)^64 ≤ (10017370612210809/10000000000000000 : ℝ)^271 := by
      have hnat : (12592071333031987227 : ℕ)^64*10000000000000000^271 ≤ 10017370612210809^271*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12592071333031987227 12500000000000000000 10017370612210809 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017370612210809/10000000000000000 : ℝ)) (X := (12592071333031987227/12500000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3011025954577/100000000000000000000 : ℝ) ≤ ((2469712132486630971/2470000000000000000 : ℝ)+2*(42996212853/12350000000000 : ℝ)*(837/50000 : ℝ))^(271/64 : ℝ) := by
    rw [show (2469712132486630971/2470000000000000000 : ℝ)+2*(42996212853/12350000000000 : ℝ)*(837/50000 : ℝ)=(10000000142218197/10000000000000000 : ℝ) by norm_num, show 1+2*(3011025954577/100000000000000000000 : ℝ)=(50000003011025954577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(92071333031987227/25000000000000000000 : ℝ)+(3011025954577/100000000000000000000 : ℝ) ≤ ((2469712132486630971/2470000000000000000 : ℝ)+(42996212853/12350000000000 : ℝ)*((26621/100000 : ℝ)+(837/50000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (2469712132486630971/2470000000000000000 : ℝ)+(42996212853/12350000000000 : ℝ)*((26621/100000 : ℝ)+(837/50000 : ℝ))=(10008685377214503/10000000000000000 : ℝ) by norm_num, show 1+(92071333031987227/25000000000000000000 : ℝ)+(3011025954577/100000000000000000000 : ℝ)=(20073657668630780697/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(92071333031987227/25000000000000000000 : ℝ) ≤ ((2469712132486630971/2470000000000000000 : ℝ)+2*(42996212853/12350000000000 : ℝ)*(26621/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (2469712132486630971/2470000000000000000 : ℝ)+2*(42996212853/12350000000000 : ℝ)*(26621/100000 : ℝ)=(10017370612210809/10000000000000000 : ℝ) by norm_num, show 1+2*(92071333031987227/25000000000000000000 : ℝ)=(12592071333031987227/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2469712132486630971/2470000000000000000 : ℝ)*(X 1 0+X 2 0)+(42996212853/12350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (837/50000 : ℝ)) (hi := (26621/100000 : ℝ)) (c := (2469712132486630971/2470000000000000000 : ℝ)) (alpha := (42996212853/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2469712132486630971/2470000000000000000 : ℝ)*(X 0 1+X 2 1)+(42996212853/12350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (837/50000 : ℝ)) (hi := (26621/100000 : ℝ)) (c := (2469712132486630971/2470000000000000000 : ℝ)) (alpha := (42996212853/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2469712132486630971/2470000000000000000 : ℝ)*(X 0 2+X 1 2)+(42996212853/12350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (837/50000 : ℝ)) (hi := (26621/100000 : ℝ)) (c := (2469712132486630971/2470000000000000000 : ℝ)) (alpha := (42996212853/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-61512981/312500000 : ℝ)*X 0 0+(351673271/625000000 : ℝ)*X 0 1+(2529591049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5402089917/10000000000 : ℝ)*X 1 0+(-2270408649/10000000000 : ℝ)*X 1 1+(5059183493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701045259/5000000000 : ℝ)*X 2 0+(5059182289/10000000000 : ℝ)*X 2 1+(-1135204703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143022153/5000000000 : ℝ)*X 0 0+(3722404327/10000000000 : ℝ)*X 0 1+(985386467/2000000000 : ℝ)*X 0 2+(2143022153/5000000000 : ℝ)*X 1 0+(3722404327/10000000000 : ℝ)*X 1 1+(985386467/2000000000 : ℝ)*X 1 2+(2143022153/5000000000 : ℝ)*X 2 0+(3722404327/10000000000 : ℝ)*X 2 1+(985386467/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-246111413/1250000000 : ℝ)*X 0 0+(1266528551/2500000000 : ℝ)*X 0 1+(5619717569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262719327/500000000 : ℝ)*X 1 0+(-854937179/5000000000 : ℝ)*X 1 1+(561971767/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313596609/2500000000 : ℝ)*X 2 0+(5619717781/10000000000 : ℝ)*X 2 1+(-341974869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143527507/5000000000 : ℝ)*X 0 0+(4912223029/10000000000 : ℝ)*X 0 1+(747474519/2000000000 : ℝ)*X 0 2+(2143527507/5000000000 : ℝ)*X 1 0+(4912223029/10000000000 : ℝ)*X 1 1+(747474519/2000000000 : ℝ)*X 1 2+(2143527507/5000000000 : ℝ)*X 2 0+(4912223029/10000000000 : ℝ)*X 2 1+(747474519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1032089617083207322701351/325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327460369/100000000000000 : ℝ)*(base19) + (22410547/4000000000000 : ℝ)*(base23) + (10665577/25000000000000 : ℝ)*(upper2) + (4367361/20000000000000 : ℝ)*(upper3) + (64801302246871/5000000000000 : ℝ)*(major0) + (64801302246871/5000000000000 : ℝ)*(major1) + (64801302246871/5000000000000 : ℝ)*(major2) + (70473651925721/4000000000000 : ℝ)*(sp0) + (880923926097491/50000000000000 : ℝ)*(sp1) + (220230759581373/12500000000000 : ℝ)*(sp2) + (83020211792663/10000000000000 : ℝ)*(sp3) + (3440756163/50000000000000 : ℝ)*(sp4) + (385685173/25000000000000 : ℝ)*(sp6) + (421609377/25000000000000 : ℝ)*(sp7) + (415101902182069/50000000000000 : ℝ)*(f.failure) + (1761848179655351/100000000000000 : ℝ)*(f.sum) + (390917523333/61750000000000000000000000 : ℝ)*base66 + (63684969969058259/12350000000000000000000000000000 : ℝ)*base68 + (22910970827858259/12350000000000000000000000000000 : ℝ)*base70 + (42261372358058259/12350000000000000000000000000000 : ℝ)*base72 + (15918135657/7718750000000000000000000 : ℝ)*base74 + (76213696575558259/12350000000000000000000000000000 : ℝ)*base76 + (160717964943558259/12350000000000000000000000000000 : ℝ)*base78 + (88395244230458259/12350000000000000000000000000000 : ℝ)*base80 + (237769581701/123500000000000000000000000 : ℝ)*base81 + (5929437/625000000000000000000 : ℝ)*base89 + (5929437/625000000000000000000 : ℝ)*base91 + (5929437/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133401873916484051509470171/15437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86634311/100000000000000 : ℝ)*(base1) + (1730728633/100000000000000 : ℝ)*(base19) + (1698148269/100000000000000 : ℝ)*(base23) + (206961693/100000000000000 : ℝ)*(upper3) + (193207349/100000000000000 : ℝ)*(upper5) + (166094978921689/12500000000000 : ℝ)*(major0) + (166094978921689/12500000000000 : ℝ)*(major1) + (166094978921689/12500000000000 : ℝ)*(major2) + (1857886289/20000000000000 : ℝ)*(sp1) + (9402248557/100000000000000 : ℝ)*(sp2) + (903173581607133/50000000000000 : ℝ)*(sp4) + (1806336056419877/100000000000000 : ℝ)*(sp5) + (225791997022891/12500000000000 : ℝ)*(sp6) + (10639652643569/1250000000000 : ℝ)*(sp7) + (851172298119831/100000000000000 : ℝ)*(f.failure) + (903173538289977/50000000000000 : ℝ)*(f.sum) + (34168684509/38593750000000000000000000 : ℝ)*base66 + (253757370076569981/30875000000000000000000000000000 : ℝ)*base68 + (194455430610319981/30875000000000000000000000000000 : ℝ)*base70 + (158419031264944981/30875000000000000000000000000000 : ℝ)*base72 + (5751081712143/1235000000000000000000000000 : ℝ)*base74 + (332269840783694981/30875000000000000000000000000000 : ℝ)*base76 + (111169125787819981/30875000000000000000000000000000 : ℝ)*base78 + (68691745603944981/30875000000000000000000000000000 : ℝ)*base80 + (2922401565779/617500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (3050737/1250000000000000000000 : ℝ)*base90 + (3050737/1250000000000000000000 : ℝ)*base92 + (3050737/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (901/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3841/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_s2_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002804639/5000000000 : ℝ)*x 0 + (5470543149/10000000000 : ℝ)*x 1 + (5191539521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002804639/5000000000 : ℝ)^4337 ≤ (1220621015963/10000000000000 : ℝ)^3313 := by
    have hnat : (1002804639 : ℕ)^4337*10000000000000^3313 ≤ 1220621015963^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002804639 5000000000 1220621015963 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470543149/10000000000 : ℝ)^4337 ≤ (22700189511827/50000000000000 : ℝ)^3313 := by
    have hnat : (5470543149 : ℕ)^4337*50000000000000^3313 ≤ 22700189511827^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470543149 10000000000 22700189511827 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191539521/10000000000 : ℝ)^4337 ≤ (26495881753/62500000000 : ℝ)^3313 := by
    have hnat : (5191539521 : ℕ)^4337*62500000000^3313 ≤ 26495881753^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191539521 10000000000 26495881753 62500000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002804639/5000000000 : ℝ), (5470543149/10000000000 : ℝ), (5191539521/10000000000 : ℝ)] ![(1220621015963/10000000000000 : ℝ), (22700189511827/50000000000000 : ℝ), (26495881753/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002804639/5000000000 : ℝ)|^4337 ≤ (1220621015963/10000000000000 : ℝ)^3313
        have hw : |(-1002804639/5000000000 : ℝ)|=(1002804639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470543149/10000000000 : ℝ)|^4337 ≤ (22700189511827/50000000000000 : ℝ)^3313
        have hw : |(5470543149/10000000000 : ℝ)|=(5470543149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191539521/10000000000 : ℝ)|^4337 ≤ (26495881753/62500000000 : ℝ)^3313
        have hw : |(5191539521/10000000000 : ℝ)|=(5191539521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363540617/10000000000 : ℝ)*x 0 + (-2149507339/10000000000 : ℝ)*x 1 + (5191539589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363540617/10000000000 : ℝ)^4337 ≤ (44241414056567/100000000000000 : ℝ)^3313 := by
    have hnat : (5363540617 : ℕ)^4337*100000000000000^3313 ≤ 44241414056567^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363540617 10000000000 44241414056567 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149507339/10000000000 : ℝ)^4337 ≤ (13365174394809/100000000000000 : ℝ)^3313 := by
    have hnat : (2149507339 : ℕ)^4337*100000000000000^3313 ≤ 13365174394809^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149507339 10000000000 13365174394809 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191539589/10000000000 : ℝ)^4337 ≤ (42393411531707/100000000000000 : ℝ)^3313 := by
    have hnat : (5191539589 : ℕ)^4337*100000000000000^3313 ≤ 42393411531707^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191539589 10000000000 42393411531707 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363540617/10000000000 : ℝ), (-2149507339/10000000000 : ℝ), (5191539589/10000000000 : ℝ)] ![(44241414056567/100000000000000 : ℝ), (13365174394809/100000000000000 : ℝ), (42393411531707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363540617/10000000000 : ℝ)|^4337 ≤ (44241414056567/100000000000000 : ℝ)^3313
        have hw : |(5363540617/10000000000 : ℝ)|=(5363540617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149507339/10000000000 : ℝ)|^4337 ≤ (13365174394809/100000000000000 : ℝ)^3313
        have hw : |(-2149507339/10000000000 : ℝ)|=(2149507339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191539589/10000000000 : ℝ)|^4337 ≤ (42393411531707/100000000000000 : ℝ)^3313
        have hw : |(5191539589/10000000000 : ℝ)|=(5191539589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363540549/10000000000 : ℝ)*x 0 + (2595769823/5000000000 : ℝ)*x 1 + (-1074753677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363540549/10000000000 : ℝ)^4337 ≤ (442414133223/1000000000000 : ℝ)^3313 := by
    have hnat : (5363540549 : ℕ)^4337*1000000000000^3313 ≤ 442414133223^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363540549 10000000000 442414133223 1000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2595769823/5000000000 : ℝ)^4337 ≤ (21196706070513/50000000000000 : ℝ)^3313 := by
    have hnat : (2595769823 : ℕ)^4337*50000000000000^3313 ≤ 21196706070513^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595769823 5000000000 21196706070513 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074753677/5000000000 : ℝ)^4337 ≤ (13365174516903/100000000000000 : ℝ)^3313 := by
    have hnat : (1074753677 : ℕ)^4337*100000000000000^3313 ≤ 13365174516903^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074753677 5000000000 13365174516903 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363540549/10000000000 : ℝ), (2595769823/5000000000 : ℝ), (-1074753677/5000000000 : ℝ)] ![(442414133223/1000000000000 : ℝ), (21196706070513/50000000000000 : ℝ), (13365174516903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363540549/10000000000 : ℝ)|^4337 ≤ (442414133223/1000000000000 : ℝ)^3313
        have hw : |(5363540549/10000000000 : ℝ)|=(5363540549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2595769823/5000000000 : ℝ)|^4337 ≤ (21196706070513/50000000000000 : ℝ)^3313
        have hw : |(2595769823/5000000000 : ℝ)|=(2595769823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074753677/5000000000 : ℝ)|^4337 ≤ (13365174516903/100000000000000 : ℝ)^3313
        have hw : |(-1074753677/5000000000 : ℝ)|=(1074753677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156078621/5000000000 : ℝ)*x 0 + (402543803/1000000000 : ℝ)*x 1 + (923507169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156078621/5000000000 : ℝ)^4337 ≤ (33249415270593/100000000000000 : ℝ)^3313 := by
    have hnat : (2156078621 : ℕ)^4337*100000000000000^3313 ≤ 33249415270593^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156078621 5000000000 33249415270593 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402543803/1000000000 : ℝ)^4337 ≤ (15192759189399/50000000000000 : ℝ)^3313 := by
    have hnat : (402543803 : ℕ)^4337*50000000000000^3313 ≤ 15192759189399^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402543803 1000000000 15192759189399 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923507169/2000000000 : ℝ)^4337 ≤ (1454602653499/4000000000000 : ℝ)^3313 := by
    have hnat : (923507169 : ℕ)^4337*4000000000000^3313 ≤ 1454602653499^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923507169 2000000000 1454602653499 4000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156078621/5000000000 : ℝ), (402543803/1000000000 : ℝ), (923507169/2000000000 : ℝ)] ![(33249415270593/100000000000000 : ℝ), (15192759189399/50000000000000 : ℝ), (1454602653499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156078621/5000000000 : ℝ)|^4337 ≤ (33249415270593/100000000000000 : ℝ)^3313
        have hw : |(2156078621/5000000000 : ℝ)|=(2156078621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402543803/1000000000 : ℝ)|^4337 ≤ (15192759189399/50000000000000 : ℝ)^3313
        have hw : |(402543803/1000000000 : ℝ)|=(402543803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923507169/2000000000 : ℝ)|^4337 ≤ (1454602653499/4000000000000 : ℝ)^3313
        have hw : |(923507169/2000000000 : ℝ)|=(923507169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005665647/10000000000 : ℝ)*x 0 + (2596612181/5000000000 : ℝ)*x 1 + (5468843847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005665647/10000000000 : ℝ)^4337 ≤ (3051664815337/25000000000000 : ℝ)^3313 := by
    have hnat : (2005665647 : ℕ)^4337*25000000000000^3313 ≤ 3051664815337^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005665647 10000000000 3051664815337 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596612181/5000000000 : ℝ)^4337 ≤ (10602855586579/25000000000000 : ℝ)^3313 := by
    have hnat : (2596612181 : ℕ)^4337*25000000000000^3313 ≤ 10602855586579^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596612181 5000000000 10602855586579 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468843847/10000000000 : ℝ)^4337 ≤ (5672739798053/12500000000000 : ℝ)^3313 := by
    have hnat : (5468843847 : ℕ)^4337*12500000000000^3313 ≤ 5672739798053^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468843847 10000000000 5672739798053 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005665647/10000000000 : ℝ), (2596612181/5000000000 : ℝ), (5468843847/10000000000 : ℝ)] ![(3051664815337/25000000000000 : ℝ), (10602855586579/25000000000000 : ℝ), (5672739798053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005665647/10000000000 : ℝ)|^4337 ≤ (3051664815337/25000000000000 : ℝ)^3313
        have hw : |(-2005665647/10000000000 : ℝ)|=(2005665647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596612181/5000000000 : ℝ)|^4337 ≤ (10602855586579/25000000000000 : ℝ)^3313
        have hw : |(2596612181/5000000000 : ℝ)|=(2596612181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468843847/10000000000 : ℝ)|^4337 ≤ (5672739798053/12500000000000 : ℝ)^3313
        have hw : |(5468843847/10000000000 : ℝ)|=(5468843847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165355023/312500000 : ℝ)*x 0 + (-117012729/625000000 : ℝ)*x 1 + (1367210887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165355023/312500000 : ℝ)^4337 ≤ (43463637974339/100000000000000 : ℝ)^3313 := by
    have hnat : (165355023 : ℕ)^4337*100000000000000^3313 ≤ 43463637974339^3313*312500000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165355023 312500000 43463637974339 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117012729/625000000 : ℝ)^4337 ≤ (11154446877911/100000000000000 : ℝ)^3313 := by
    have hnat : (117012729 : ℕ)^4337*100000000000000^3313 ≤ 11154446877911^3313*625000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117012729 625000000 11154446877911 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367210887/2500000000 : ℝ)^4337 ≤ (22690957568173/50000000000000 : ℝ)^3313 := by
    have hnat : (1367210887 : ℕ)^4337*50000000000000^3313 ≤ 22690957568173^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367210887 2500000000 22690957568173 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165355023/312500000 : ℝ), (-117012729/625000000 : ℝ), (1367210887/2500000000 : ℝ)] ![(43463637974339/100000000000000 : ℝ), (11154446877911/100000000000000 : ℝ), (22690957568173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165355023/312500000 : ℝ)|^4337 ≤ (43463637974339/100000000000000 : ℝ)^3313
        have hw : |(165355023/312500000 : ℝ)|=(165355023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117012729/625000000 : ℝ)|^4337 ≤ (11154446877911/100000000000000 : ℝ)^3313
        have hw : |(-117012729/625000000 : ℝ)|=(117012729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367210887/2500000000 : ℝ)|^4337 ≤ (22690957568173/50000000000000 : ℝ)^3313
        have hw : |(1367210887/2500000000 : ℝ)|=(1367210887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330710139/625000000 : ℝ)*x 0 + (683605457/1250000000 : ℝ)*x 1 + (-936100731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330710139/625000000 : ℝ)^4337 ≤ (8692730794939/20000000000000 : ℝ)^3313 := by
    have hnat : (330710139 : ℕ)^4337*20000000000000^3313 ≤ 8692730794939^3313*625000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330710139 625000000 8692730794939 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683605457/1250000000 : ℝ)^4337 ≤ (9076383261913/20000000000000 : ℝ)^3313 := by
    have hnat : (683605457 : ℕ)^4337*20000000000000^3313 ≤ 9076383261913^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683605457 1250000000 9076383261913 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936100731/5000000000 : ℝ)^4337 ≤ (11154429703567/100000000000000 : ℝ)^3313 := by
    have hnat : (936100731 : ℕ)^4337*100000000000000^3313 ≤ 11154429703567^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936100731 5000000000 11154429703567 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330710139/625000000 : ℝ), (683605457/1250000000 : ℝ), (-936100731/5000000000 : ℝ)] ![(8692730794939/20000000000000 : ℝ), (9076383261913/20000000000000 : ℝ), (11154429703567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330710139/625000000 : ℝ)|^4337 ≤ (8692730794939/20000000000000 : ℝ)^3313
        have hw : |(330710139/625000000 : ℝ)|=(330710139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683605457/1250000000 : ℝ)|^4337 ≤ (9076383261913/20000000000000 : ℝ)^3313
        have hw : |(683605457/1250000000 : ℝ)|=(683605457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936100731/5000000000 : ℝ)|^4337 ≤ (11154429703567/100000000000000 : ℝ)^3313
        have hw : |(-936100731/5000000000 : ℝ)|=(936100731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s2_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431227857/1000000000 : ℝ)*x 0 + (4613961021/10000000000 : ℝ)*x 1 + (4029042859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431227857/1000000000 : ℝ)^4337 ≤ (16625319972069/50000000000000 : ℝ)^3313 := by
    have hnat : (431227857 : ℕ)^4337*50000000000000^3313 ≤ 16625319972069^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431227857 1000000000 16625319972069 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4613961021/10000000000 : ℝ)^4337 ≤ (1816410785927/5000000000000 : ℝ)^3313 := by
    have hnat : (4613961021 : ℕ)^4337*5000000000000^3313 ≤ 1816410785927^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4613961021 10000000000 1816410785927 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029042859/10000000000 : ℝ)^4337 ≤ (3802643038973/12500000000000 : ℝ)^3313 := by
    have hnat : (4029042859 : ℕ)^4337*12500000000000^3313 ≤ 3802643038973^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029042859 10000000000 3802643038973 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431227857/1000000000 : ℝ), (4613961021/10000000000 : ℝ), (4029042859/10000000000 : ℝ)] ![(16625319972069/50000000000000 : ℝ), (1816410785927/5000000000000 : ℝ), (3802643038973/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431227857/1000000000 : ℝ)|^4337 ≤ (16625319972069/50000000000000 : ℝ)^3313
        have hw : |(431227857/1000000000 : ℝ)|=(431227857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4613961021/10000000000 : ℝ)|^4337 ≤ (1816410785927/5000000000000 : ℝ)^3313
        have hw : |(4613961021/10000000000 : ℝ)|=(4613961021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029042859/10000000000 : ℝ)|^4337 ≤ (3802643038973/12500000000000 : ℝ)^3313
        have hw : |(4029042859/10000000000 : ℝ)|=(4029042859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3841/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (901/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1259/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3993/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3841/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (901/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3841/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (901/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3841/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (901/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3841/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (901/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3841/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (901/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3841/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (901/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (901/12500 : ℝ) ^ (271/64 : ℝ) ≤ (145733518535247/10000000000000000000 : ℝ) := by
    have hpowers : (901/12500 : ℝ)^271 ≤ (145733518535247/10000000000000000000 : ℝ)^64 := by
      have hnat : (901 : ℕ)^271*10000000000000000000^64 ≤ 145733518535247^64*12500^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        901 12500 145733518535247 10000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (901/12500 : ℝ)) (X := (145733518535247/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3841/20000 : ℝ) ^ (271/64 : ℝ) ≤ (46203777054265167/50000000000000000000 : ℝ) := by
    have hpowers : (3841/20000 : ℝ)^271 ≤ (46203777054265167/50000000000000000000 : ℝ)^64 := by
      have hnat : (3841 : ℕ)^271*50000000000000000000^64 ≤ 46203777054265167^64*20000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3841 20000 46203777054265167 50000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3841/20000 : ℝ)) (X := (46203777054265167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000145733518535247/5000000000000000000 : ℝ) ≤ (10000068832777591/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (5000145733518535247/5000000000000000000 : ℝ)^64 ≤ (10000068832777591/10000000000000000 : ℝ)^271 := by
      have hnat : (5000145733518535247 : ℕ)^64*10000000000000000^271 ≤ 10000068832777591^271*5000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000145733518535247 5000000000000000000 10000068832777591 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000068832777591/10000000000000000 : ℝ)) (X := (5000145733518535247/5000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25023466222323470701/25000000000000000000 : ℝ) ≤ (10002215941158873/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (25023466222323470701/25000000000000000000 : ℝ)^64 ≤ (10002215941158873/10000000000000000 : ℝ)^271 := by
      have hnat : (25023466222323470701 : ℕ)^64*10000000000000000^271 ≤ 10002215941158873^271*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023466222323470701 25000000000000000000 10002215941158873 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002215941158873/10000000000000000 : ℝ)) (X := (25023466222323470701/25000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25046203777054265167/25000000000000000000 : ℝ) ≤ (2000872609908031/2000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (25046203777054265167/25000000000000000000 : ℝ)^64 ≤ (2000872609908031/2000000000000000 : ℝ)^271 := by
      have hnat : (25046203777054265167 : ℕ)^64*2000000000000000^271 ≤ 2000872609908031^271*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25046203777054265167 25000000000000000000 2000872609908031 2000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000872609908031/2000000000000000 : ℝ)) (X := (25046203777054265167/25000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(145733518535247/10000000000000000000 : ℝ) ≤ ((23987974614481639583/23994000000000000000 : ℝ)+2*(1073554190641/599850000000000 : ℝ)*(901/12500 : ℝ))^(271/64 : ℝ) := by
    rw [show (23987974614481639583/23994000000000000000 : ℝ)+2*(1073554190641/599850000000000 : ℝ)*(901/12500 : ℝ)=(10000068832777591/10000000000000000 : ℝ) by norm_num, show 1+2*(145733518535247/10000000000000000000 : ℝ)=(5000145733518535247/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46203777054265167/50000000000000000000 : ℝ)+(145733518535247/10000000000000000000 : ℝ) ≤ ((23987974614481639583/23994000000000000000 : ℝ)+(1073554190641/599850000000000 : ℝ)*((3841/20000 : ℝ)+(901/12500 : ℝ)))^(271/64 : ℝ) := by
    rw [show (23987974614481639583/23994000000000000000 : ℝ)+(1073554190641/599850000000000 : ℝ)*((3841/20000 : ℝ)+(901/12500 : ℝ))=(10002215941158873/10000000000000000 : ℝ) by norm_num, show 1+(46203777054265167/50000000000000000000 : ℝ)+(145733518535247/10000000000000000000 : ℝ)=(25023466222323470701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46203777054265167/50000000000000000000 : ℝ) ≤ ((23987974614481639583/23994000000000000000 : ℝ)+2*(1073554190641/599850000000000 : ℝ)*(3841/20000 : ℝ))^(271/64 : ℝ) := by
    rw [show (23987974614481639583/23994000000000000000 : ℝ)+2*(1073554190641/599850000000000 : ℝ)*(3841/20000 : ℝ)=(2000872609908031/2000000000000000 : ℝ) by norm_num, show 1+2*(46203777054265167/50000000000000000000 : ℝ)=(25046203777054265167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23987974614481639583/23994000000000000000 : ℝ)*(X 1 0+X 2 0)+(1073554190641/599850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (901/12500 : ℝ)) (hi := (3841/20000 : ℝ)) (c := (23987974614481639583/23994000000000000000 : ℝ)) (alpha := (1073554190641/599850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23987974614481639583/23994000000000000000 : ℝ)*(X 0 1+X 2 1)+(1073554190641/599850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (901/12500 : ℝ)) (hi := (3841/20000 : ℝ)) (c := (23987974614481639583/23994000000000000000 : ℝ)) (alpha := (1073554190641/599850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23987974614481639583/23994000000000000000 : ℝ)*(X 0 2+X 1 2)+(1073554190641/599850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (901/12500 : ℝ)) (hi := (3841/20000 : ℝ)) (c := (23987974614481639583/23994000000000000000 : ℝ)) (alpha := (1073554190641/599850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1002804639/5000000000 : ℝ)*X 0 0+(5470543149/10000000000 : ℝ)*X 0 1+(5191539521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363540617/10000000000 : ℝ)*X 1 0+(-2149507339/10000000000 : ℝ)*X 1 1+(5191539589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363540549/10000000000 : ℝ)*X 2 0+(2595769823/5000000000 : ℝ)*X 2 1+(-1074753677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156078621/5000000000 : ℝ)*X 0 0+(402543803/1000000000 : ℝ)*X 0 1+(923507169/2000000000 : ℝ)*X 0 2+(2156078621/5000000000 : ℝ)*X 1 0+(402543803/1000000000 : ℝ)*X 1 1+(923507169/2000000000 : ℝ)*X 1 2+(2156078621/5000000000 : ℝ)*X 2 0+(402543803/1000000000 : ℝ)*X 2 1+(923507169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2005665647/10000000000 : ℝ)*X 0 0+(2596612181/5000000000 : ℝ)*X 0 1+(5468843847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165355023/312500000 : ℝ)*X 1 0+(-117012729/625000000 : ℝ)*X 1 1+(1367210887/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330710139/625000000 : ℝ)*X 2 0+(683605457/1250000000 : ℝ)*X 2 1+(-936100731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431227857/1000000000 : ℝ)*X 0 0+(4613961021/10000000000 : ℝ)*X 0 1+(4029042859/10000000000 : ℝ)*X 0 2+(431227857/1000000000 : ℝ)*X 1 0+(4613961021/10000000000 : ℝ)*X 1 1+(4029042859/10000000000 : ℝ)*X 1 2+(431227857/1000000000 : ℝ)*X 2 0+(4613961021/10000000000 : ℝ)*X 2 1+(4029042859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (441013303014759687824153429/66650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1134388081/100000000000000 : ℝ)*(base19) + (1003079817/100000000000000 : ℝ)*(base23) + (46055083/100000000000000 : ℝ)*(lower2) + (8996343/5000000000000 : ℝ)*(upper3) + (11198307/12500000000000 : ℝ)*(upper5) + (1318284042692111/50000000000000 : ℝ)*(major0) + (1318284042692111/50000000000000 : ℝ)*(major1) + (1318284042692111/50000000000000 : ℝ)*(major2) + (3584198380894601/100000000000000 : ℝ)*(sp0) + (716842261459397/20000000000000 : ℝ)*(sp1) + (14336845754421/400000000000 : ℝ)*(sp2) + (168891629834711/10000000000000 : ℝ)*(sp3) + (2812158093/20000000000000 : ℝ)*(sp4) + (7210174467/100000000000000 : ℝ)*(sp7) + (1688923508521577/100000000000000 : ℝ)*(f.failure) + (1792106220842533/50000000000000 : ℝ)*(f.sum) + (120920712995759/59985000000000000000000000000 : ℝ)*base65 + (5603046266653756571/399900000000000000000000000000000 : ℝ)*base67 + (3942344308763056571/399900000000000000000000000000000 : ℝ)*base69 + (1817876168210656571/399900000000000000000000000000000 : ℝ)*base71 + (81640437745121/14996250000000000000000000000 : ℝ)*base73 + (3418757562581956571/399900000000000000000000000000000 : ℝ)*base75 + (121695819538843429/399900000000000000000000000000000 : ℝ)*base78 + (1000020402284143429/399900000000000000000000000000000 : ℝ)*base80 + (78364251211649/59985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7977679/1250000000000000000000 : ℝ)*base90 + (7977679/1250000000000000000000 : ℝ)*base92 + (7977679/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57112374414796317646116439/13330000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3348809/400000000000 : ℝ)*(base19) + (762781329/25000000000000 : ℝ)*(base23) + (1839717/50000000000000 : ℝ)*(lower2) + (135433313/50000000000000 : ℝ)*(upper3) + (79462063/25000000000000 : ℝ)*(lower4) + (499661/3125000000000 : ℝ)*(upper5) + (266891648251701/10000000000000 : ℝ)*(major0) + (266891648251701/10000000000000 : ℝ)*(major1) + (266891648251701/10000000000000 : ℝ)*(major2) + (1759109079/4000000000000 : ℝ)*(sp2) + (725637538252837/20000000000000 : ℝ)*(sp4) + (725637370812387/20000000000000 : ℝ)*(sp5) + (3628140662411893/100000000000000 : ℝ)*(sp6) + (53426410342287/3125000000000 : ℝ)*(sp7) + (53426410342287/3125000000000 : ℝ)*(f.failure) + (725637538252837/20000000000000 : ℝ)*(f.sum) + (61034600852027/3999000000000000000000000000 : ℝ)*base66 + (6693669560848813/26660000000000000000000000000000 : ℝ)*base68 + (28200742568068813/26660000000000000000000000000000 : ℝ)*base70 + (218809001847191187/26660000000000000000000000000000 : ℝ)*base71 + (2355548297203/999750000000000000000000000 : ℝ)*base73 + (51021428669831187/26660000000000000000000000000000 : ℝ)*base75 + (68421137628171187/26660000000000000000000000000000 : ℝ)*base77 + (253292605937071187/26660000000000000000000000000000 : ℝ)*base79 + (226444866859/499875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (441099/39062500000000000000 : ℝ)*base90 + (441099/39062500000000000000 : ℝ)*base92 + (441099/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3841/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (901/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1377_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1377_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1377_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1377_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
