-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1236_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:12.927615+00:00
-- url     : https://prove2.me/submissions/7be1c94c-53a0-40ed-a219-189bdea56312

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
theorem support_rectangle_w1236_s3_0 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059915921/5000000000 : ℝ)*x 0 + (1355047211/2500000000 : ℝ)*x 1 + (5240153213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059915921/5000000000 : ℝ)^8429 ≤ (3221187108761/25000000000000 : ℝ)^6381 := by
    have hnat : (1059915921 : ℕ)^8429*25000000000000^6381 ≤ 3221187108761^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059915921 5000000000 3221187108761 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355047211/2500000000 : ℝ)^8429 ≤ (695769871881/1562500000000 : ℝ)^6381 := by
    have hnat : (1355047211 : ℕ)^8429*1562500000000^6381 ≤ 695769871881^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355047211 2500000000 695769871881 1562500000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240153213/10000000000 : ℝ)^8429 ≤ (42585979758893/100000000000000 : ℝ)^6381 := by
    have hnat : (5240153213 : ℕ)^8429*100000000000000^6381 ≤ 42585979758893^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240153213 10000000000 42585979758893 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059915921/5000000000 : ℝ), (1355047211/2500000000 : ℝ), (5240153213/10000000000 : ℝ)] ![(3221187108761/25000000000000 : ℝ), (695769871881/1562500000000 : ℝ), (42585979758893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059915921/5000000000 : ℝ)|^8429 ≤ (3221187108761/25000000000000 : ℝ)^6381
        have hw : |(-1059915921/5000000000 : ℝ)|=(1059915921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355047211/2500000000 : ℝ)|^8429 ≤ (695769871881/1562500000000 : ℝ)^6381
        have hw : |(1355047211/2500000000 : ℝ)|=(1355047211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240153213/10000000000 : ℝ)|^8429 ≤ (42585979758893/100000000000000 : ℝ)^6381
        have hw : |(5240153213/10000000000 : ℝ)|=(5240153213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_1 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351623477/10000000000 : ℝ)*x 0 + (-2211685177/10000000000 : ℝ)*x 1 + (2620076679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351623477/10000000000 : ℝ)^8429 ≤ (10946675099003/25000000000000 : ℝ)^6381 := by
    have hnat : (5351623477 : ℕ)^8429*25000000000000^6381 ≤ 10946675099003^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351623477 10000000000 10946675099003 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211685177/10000000000 : ℝ)^8429 ≤ (2725463654091/20000000000000 : ℝ)^6381 := by
    have hnat : (2211685177 : ℕ)^8429*20000000000000^6381 ≤ 2725463654091^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211685177 10000000000 2725463654091 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620076679/5000000000 : ℝ)^8429 ≤ (5323247664437/12500000000000 : ℝ)^6381 := by
    have hnat : (2620076679 : ℕ)^8429*12500000000000^6381 ≤ 5323247664437^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620076679 5000000000 5323247664437 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351623477/10000000000 : ℝ), (-2211685177/10000000000 : ℝ), (2620076679/5000000000 : ℝ)] ![(10946675099003/25000000000000 : ℝ), (2725463654091/20000000000000 : ℝ), (5323247664437/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351623477/10000000000 : ℝ)|^8429 ≤ (10946675099003/25000000000000 : ℝ)^6381
        have hw : |(5351623477/10000000000 : ℝ)|=(5351623477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211685177/10000000000 : ℝ)|^8429 ≤ (2725463654091/20000000000000 : ℝ)^6381
        have hw : |(-2211685177/10000000000 : ℝ)|=(2211685177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620076679/5000000000 : ℝ)|^8429 ≤ (5323247664437/12500000000000 : ℝ)^6381
        have hw : |(2620076679/5000000000 : ℝ)|=(2620076679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_2 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267581169/500000000 : ℝ)*x 0 + (327509611/625000000 : ℝ)*x 1 + (-1105842377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267581169/500000000 : ℝ)^8429 ≤ (1094667483691/2500000000000 : ℝ)^6381 := by
    have hnat : (267581169 : ℕ)^8429*2500000000000^6381 ≤ 1094667483691^6381*500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267581169 500000000 1094667483691 2500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327509611/625000000 : ℝ)^8429 ≤ (5323248225351/12500000000000 : ℝ)^6381 := by
    have hnat : (327509611 : ℕ)^8429*12500000000000^6381 ≤ 5323248225351^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327509611 625000000 5323248225351 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105842377/5000000000 : ℝ)^8429 ≤ (851707176727/6250000000000 : ℝ)^6381 := by
    have hnat : (1105842377 : ℕ)^8429*6250000000000^6381 ≤ 851707176727^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105842377 5000000000 851707176727 6250000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267581169/500000000 : ℝ), (327509611/625000000 : ℝ), (-1105842377/5000000000 : ℝ)] ![(1094667483691/2500000000000 : ℝ), (5323248225351/12500000000000 : ℝ), (851707176727/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267581169/500000000 : ℝ)|^8429 ≤ (1094667483691/2500000000000 : ℝ)^6381
        have hw : |(267581169/500000000 : ℝ)|=(267581169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327509611/625000000 : ℝ)|^8429 ≤ (5323248225351/12500000000000 : ℝ)^6381
        have hw : |(327509611/625000000 : ℝ)|=(327509611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105842377/5000000000 : ℝ)|^8429 ≤ (851707176727/6250000000000 : ℝ)^6381
        have hw : |(-1105842377/5000000000 : ℝ)|=(1105842377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_3 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087467173/2500000000 : ℝ)*x 0 + (4171192619/10000000000 : ℝ)*x 1 + (1133995807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087467173/2500000000 : ℝ)^8429 ≤ (520312273041/1562500000000 : ℝ)^6381 := by
    have hnat : (1087467173 : ℕ)^8429*1562500000000^6381 ≤ 520312273041^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087467173 2500000000 520312273041 1562500000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171192619/10000000000 : ℝ)^8429 ≤ (393814506677/1250000000000 : ℝ)^6381 := by
    have hnat : (4171192619 : ℕ)^8429*1250000000000^6381 ≤ 393814506677^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171192619 10000000000 393814506677 1250000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133995807/2500000000 : ℝ)^8429 ≤ (17597426985081/50000000000000 : ℝ)^6381 := by
    have hnat : (1133995807 : ℕ)^8429*50000000000000^6381 ≤ 17597426985081^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133995807 2500000000 17597426985081 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087467173/2500000000 : ℝ), (4171192619/10000000000 : ℝ), (1133995807/2500000000 : ℝ)] ![(520312273041/1562500000000 : ℝ), (393814506677/1250000000000 : ℝ), (17597426985081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087467173/2500000000 : ℝ)|^8429 ≤ (520312273041/1562500000000 : ℝ)^6381
        have hw : |(1087467173/2500000000 : ℝ)|=(1087467173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171192619/10000000000 : ℝ)|^8429 ≤ (393814506677/1250000000000 : ℝ)^6381
        have hw : |(4171192619/10000000000 : ℝ)|=(4171192619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133995807/2500000000 : ℝ)|^8429 ≤ (17597426985081/50000000000000 : ℝ)^6381
        have hw : |(1133995807/2500000000 : ℝ)|=(1133995807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_4 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119846151/10000000000 : ℝ)*x 0 + (5240810087/10000000000 : ℝ)*x 1 + (135488211/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119846151/10000000000 : ℝ)^8429 ≤ (12884863322231/100000000000000 : ℝ)^6381 := by
    have hnat : (2119846151 : ℕ)^8429*100000000000000^6381 ≤ 12884863322231^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119846151 10000000000 12884863322231 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240810087/10000000000 : ℝ)^8429 ≤ (21296515785853/50000000000000 : ℝ)^6381 := by
    have hnat : (5240810087 : ℕ)^8429*50000000000000^6381 ≤ 21296515785853^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240810087 10000000000 21296515785853 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135488211/250000000 : ℝ)^8429 ≤ (11130526273189/25000000000000 : ℝ)^6381 := by
    have hnat : (135488211 : ℕ)^8429*25000000000000^6381 ≤ 11130526273189^6381*250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135488211 250000000 11130526273189 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119846151/10000000000 : ℝ), (5240810087/10000000000 : ℝ), (135488211/250000000 : ℝ)] ![(12884863322231/100000000000000 : ℝ), (21296515785853/50000000000000 : ℝ), (11130526273189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119846151/10000000000 : ℝ)|^8429 ≤ (12884863322231/100000000000000 : ℝ)^6381
        have hw : |(-2119846151/10000000000 : ℝ)|=(2119846151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240810087/10000000000 : ℝ)|^8429 ≤ (21296515785853/50000000000000 : ℝ)^6381
        have hw : |(5240810087/10000000000 : ℝ)|=(5240810087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135488211/250000000 : ℝ)|^8429 ≤ (11130526273189/25000000000000 : ℝ)^6381
        have hw : |(135488211/250000000 : ℝ)|=(135488211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_5 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663213767/1250000000 : ℝ)*x 0 + (-406462101/2000000000 : ℝ)*x 1 + (5419528501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663213767/1250000000 : ℝ)^8429 ≤ (21645577544203/50000000000000 : ℝ)^6381 := by
    have hnat : (663213767 : ℕ)^8429*50000000000000^6381 ≤ 21645577544203^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663213767 1250000000 21645577544203 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406462101/2000000000 : ℝ)^8429 ≤ (12186739136831/100000000000000 : ℝ)^6381 := by
    have hnat : (406462101 : ℕ)^8429*100000000000000^6381 ≤ 12186739136831^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406462101 2000000000 12186739136831 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419528501/10000000000 : ℝ)^8429 ≤ (8904421150943/20000000000000 : ℝ)^6381 := by
    have hnat : (5419528501 : ℕ)^8429*20000000000000^6381 ≤ 8904421150943^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419528501 10000000000 8904421150943 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663213767/1250000000 : ℝ), (-406462101/2000000000 : ℝ), (5419528501/10000000000 : ℝ)] ![(21645577544203/50000000000000 : ℝ), (12186739136831/100000000000000 : ℝ), (8904421150943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663213767/1250000000 : ℝ)|^8429 ≤ (21645577544203/50000000000000 : ℝ)^6381
        have hw : |(663213767/1250000000 : ℝ)|=(663213767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406462101/2000000000 : ℝ)|^8429 ≤ (12186739136831/100000000000000 : ℝ)^6381
        have hw : |(-406462101/2000000000 : ℝ)|=(406462101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419528501/10000000000 : ℝ)|^8429 ≤ (8904421150943/20000000000000 : ℝ)^6381
        have hw : |(5419528501/10000000000 : ℝ)|=(5419528501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_6 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305710551/10000000000 : ℝ)*x 0 + (169360259/312500000 : ℝ)*x 1 + (-2032310233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305710551/10000000000 : ℝ)^8429 ≤ (21645579780663/50000000000000 : ℝ)^6381 := by
    have hnat : (5305710551 : ℕ)^8429*50000000000000^6381 ≤ 21645579780663^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305710551 10000000000 21645579780663 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169360259/312500000 : ℝ)^8429 ≤ (44522103443283/100000000000000 : ℝ)^6381 := by
    have hnat : (169360259 : ℕ)^8429*100000000000000^6381 ≤ 44522103443283^6381*312500000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169360259 312500000 44522103443283 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032310233/10000000000 : ℝ)^8429 ≤ (2437347396459/20000000000000 : ℝ)^6381 := by
    have hnat : (2032310233 : ℕ)^8429*20000000000000^6381 ≤ 2437347396459^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032310233 10000000000 2437347396459 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305710551/10000000000 : ℝ), (169360259/312500000 : ℝ), (-2032310233/10000000000 : ℝ)] ![(21645579780663/50000000000000 : ℝ), (44522103443283/100000000000000 : ℝ), (2437347396459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305710551/10000000000 : ℝ)|^8429 ≤ (21645579780663/50000000000000 : ℝ)^6381
        have hw : |(5305710551/10000000000 : ℝ)|=(5305710551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169360259/312500000 : ℝ)|^8429 ≤ (44522103443283/100000000000000 : ℝ)^6381
        have hw : |(169360259/312500000 : ℝ)|=(169360259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2032310233/10000000000 : ℝ)|^8429 ≤ (2437347396459/20000000000000 : ℝ)^6381
        have hw : |(-2032310233/10000000000 : ℝ)|=(2032310233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s3_7 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174948841/5000000000 : ℝ)*x 0 + (4534652653/10000000000 : ℝ)*x 1 + (4172529969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174948841/5000000000 : ℝ)^8429 ≤ (6660055726813/20000000000000 : ℝ)^6381 := by
    have hnat : (2174948841 : ℕ)^8429*20000000000000^6381 ≤ 6660055726813^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174948841 5000000000 6660055726813 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534652653/10000000000 : ℝ)^8429 ≤ (8795304280929/25000000000000 : ℝ)^6381 := by
    have hnat : (4534652653 : ℕ)^8429*25000000000000^6381 ≤ 8795304280929^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534652653 10000000000 8795304280929 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172529969/10000000000 : ℝ)^8429 ≤ (31518504231587/100000000000000 : ℝ)^6381 := by
    have hnat : (4172529969 : ℕ)^8429*100000000000000^6381 ≤ 31518504231587^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172529969 10000000000 31518504231587 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174948841/5000000000 : ℝ), (4534652653/10000000000 : ℝ), (4172529969/10000000000 : ℝ)] ![(6660055726813/20000000000000 : ℝ), (8795304280929/25000000000000 : ℝ), (31518504231587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174948841/5000000000 : ℝ)|^8429 ≤ (6660055726813/20000000000000 : ℝ)^6381
        have hw : |(2174948841/5000000000 : ℝ)|=(2174948841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534652653/10000000000 : ℝ)|^8429 ≤ (8795304280929/25000000000000 : ℝ)^6381
        have hw : |(4534652653/10000000000 : ℝ)|=(4534652653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172529969/10000000000 : ℝ)|^8429 ≤ (31518504231587/100000000000000 : ℝ)^6381
        have hw : |(4172529969/10000000000 : ℝ)|=(4172529969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1236_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (681/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (379/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (379/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (379/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (379/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (379/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (379/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (379/4000 : ℝ) ^ (2107/512 : ℝ) ≤ (3071521960831867/50000000000000000000 : ℝ) := by
    have hpowers : (379/4000 : ℝ)^2107 ≤ (3071521960831867/50000000000000000000 : ℝ)^512 := by
      have hnat : (379 : ℕ)^2107*50000000000000000000^512 ≤ 3071521960831867^512*4000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        379 4000 3071521960831867 50000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (379/4000 : ℝ)) (X := (3071521960831867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16239/100000 : ℝ) ^ (2107/512 : ℝ) ≤ (28199176370627689/50000000000000000000 : ℝ) := by
    have hpowers : (16239/100000 : ℝ)^2107 ≤ (28199176370627689/50000000000000000000 : ℝ)^512 := by
      have hnat : (16239 : ℕ)^2107*50000000000000000000^512 ≤ 28199176370627689^512*100000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16239 100000 28199176370627689 50000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16239/100000 : ℝ)) (X := (28199176370627689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003071521960831867/25000000000000000000 : ℝ) ≤ (10000298537468989/10000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (25003071521960831867/25000000000000000000 : ℝ)^512 ≤ (10000298537468989/10000000000000000 : ℝ)^2107 := by
      have hnat : (25003071521960831867 : ℕ)^512*10000000000000000^2107 ≤ 10000298537468989^2107*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003071521960831867 25000000000000000000 10000298537468989 10000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000298537468989/10000000000000000 : ℝ)) (X := (25003071521960831867/25000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507817674582864889/12500000000000000000 : ℝ) ≤ (2000303878669489/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (12507817674582864889/12500000000000000000 : ℝ)^512 ≤ (2000303878669489/2000000000000000 : ℝ)^2107 := by
      have hnat : (12507817674582864889 : ℕ)^512*2000000000000000^2107 ≤ 2000303878669489^2107*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507817674582864889 12500000000000000000 2000303878669489 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000303878669489/2000000000000000 : ℝ)) (X := (12507817674582864889/12500000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028199176370627689/25000000000000000000 : ℝ) ≤ (10002740249225901/10000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (25028199176370627689/25000000000000000000 : ℝ)^512 ≤ (10002740249225901/10000000000000000 : ℝ)^2107 := by
      have hnat : (25028199176370627689 : ℕ)^512*10000000000000000^2107 ≤ 10002740249225901^2107*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028199176370627689 25000000000000000000 10002740249225901 10000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002740249225901/10000000000000000 : ℝ)) (X := (25028199176370627689/25000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3071521960831867/50000000000000000000 : ℝ) ≤ ((16904721022135875099/16910000000000000000 : ℝ)+2*(152606984807/84550000000000 : ℝ)*(379/4000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (16904721022135875099/16910000000000000000 : ℝ)+2*(152606984807/84550000000000 : ℝ)*(379/4000 : ℝ)=(10000298537468989/10000000000000000 : ℝ) by norm_num, show 1+2*(3071521960831867/50000000000000000000 : ℝ)=(25003071521960831867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28199176370627689/50000000000000000000 : ℝ)+(3071521960831867/50000000000000000000 : ℝ) ≤ ((16904721022135875099/16910000000000000000 : ℝ)+(152606984807/84550000000000 : ℝ)*((16239/100000 : ℝ)+(379/4000 : ℝ)))^(2107/512 : ℝ) := by
    rw [show (16904721022135875099/16910000000000000000 : ℝ)+(152606984807/84550000000000 : ℝ)*((16239/100000 : ℝ)+(379/4000 : ℝ))=(2000303878669489/2000000000000000 : ℝ) by norm_num, show 1+(28199176370627689/50000000000000000000 : ℝ)+(3071521960831867/50000000000000000000 : ℝ)=(12507817674582864889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28199176370627689/50000000000000000000 : ℝ) ≤ ((16904721022135875099/16910000000000000000 : ℝ)+2*(152606984807/84550000000000 : ℝ)*(16239/100000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (16904721022135875099/16910000000000000000 : ℝ)+2*(152606984807/84550000000000 : ℝ)*(16239/100000 : ℝ)=(10002740249225901/10000000000000000 : ℝ) by norm_num, show 1+2*(28199176370627689/50000000000000000000 : ℝ)=(25028199176370627689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16904721022135875099/16910000000000000000 : ℝ)*(X 1 0+X 2 0)+(152606984807/84550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (16904721022135875099/16910000000000000000 : ℝ)) (alpha := (152606984807/84550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16904721022135875099/16910000000000000000 : ℝ)*(X 0 1+X 2 1)+(152606984807/84550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (16904721022135875099/16910000000000000000 : ℝ)) (alpha := (152606984807/84550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16904721022135875099/16910000000000000000 : ℝ)*(X 0 2+X 1 2)+(152606984807/84550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (16904721022135875099/16910000000000000000 : ℝ)) (alpha := (152606984807/84550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1059915921/5000000000 : ℝ)*X 0 0+(1355047211/2500000000 : ℝ)*X 0 1+(5240153213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351623477/10000000000 : ℝ)*X 1 0+(-2211685177/10000000000 : ℝ)*X 1 1+(2620076679/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267581169/500000000 : ℝ)*X 2 0+(327509611/625000000 : ℝ)*X 2 1+(-1105842377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087467173/2500000000 : ℝ)*X 0 0+(4171192619/10000000000 : ℝ)*X 0 1+(1133995807/2500000000 : ℝ)*X 0 2+(1087467173/2500000000 : ℝ)*X 1 0+(4171192619/10000000000 : ℝ)*X 1 1+(1133995807/2500000000 : ℝ)*X 1 2+(1087467173/2500000000 : ℝ)*X 2 0+(4171192619/10000000000 : ℝ)*X 2 1+(1133995807/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119846151/10000000000 : ℝ)*X 0 0+(5240810087/10000000000 : ℝ)*X 0 1+(135488211/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663213767/1250000000 : ℝ)*X 1 0+(-406462101/2000000000 : ℝ)*X 1 1+(5419528501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305710551/10000000000 : ℝ)*X 2 0+(169360259/312500000 : ℝ)*X 2 1+(-2032310233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174948841/5000000000 : ℝ)*X 0 0+(4534652653/10000000000 : ℝ)*X 0 1+(4172529969/10000000000 : ℝ)*X 0 2+(2174948841/5000000000 : ℝ)*X 1 0+(4534652653/10000000000 : ℝ)*X 1 1+(4172529969/10000000000 : ℝ)*X 1 2+(2174948841/5000000000 : ℝ)*X 2 0+(4534652653/10000000000 : ℝ)*X 2 1+(4172529969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17060714085651878527377/4227500000000000000000000000 : ℝ) := by norm_num
    linear_combination (340150513/100000000000000 : ℝ)*(base19) + (11028641/100000000000000 : ℝ)*(base23) + (74742469/50000000000000 : ℝ)*(lower2) + (43174787/100000000000000 : ℝ)*(lower3) + (1036975500172127/25000000000000 : ℝ)*(major0) + (1036975500172127/25000000000000 : ℝ)*(major1) + (1036975500172127/25000000000000 : ℝ)*(major2) + (2777236816306599/50000000000000 : ℝ)*(sp0) + (173577787986999/3125000000000 : ℝ)*(sp1) + (86788991803513/1562500000000 : ℝ)*(sp2) + (1370651659216407/50000000000000 : ℝ)*(sp3) + (874153611/4000000000000 : ℝ)*(sp4) + (5930718993/100000000000000 : ℝ)*(sp5) + (202478761/4000000000000 : ℝ)*(sp7) + (2741308380401839/100000000000000 : ℝ)*(f.failure) + (5554495486453473/100000000000000 : ℝ)*(f.sum) + (5233434640777/8455000000000000000000000000 : ℝ)*base65 + (1762658812283965573/422750000000000000000000000000000 : ℝ)*base67 + (6456230985024284427/422750000000000000000000000000000 : ℝ)*base70 + (522564429845465573/422750000000000000000000000000000 : ℝ)*base71 + (13925203948269/4227500000000000000000000000 : ℝ)*base74 + (8640097396607534427/422750000000000000000000000000000 : ℝ)*base76 + (5405380809608534427/422750000000000000000000000000000 : ℝ)*base78 + (3734640193747715573/422750000000000000000000000000000 : ℝ)*base79 + (6132493751417/8455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4223481/1250000000000000000000 : ℝ)*base89 + (4223481/1250000000000000000000 : ℝ)*base91 + (4223481/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2372885487447877514794753539/422750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56122611/100000000000000 : ℝ)*(base19) + (415665087/100000000000000 : ℝ)*(base23) + (117635281/100000000000000 : ℝ)*(lower2) + (29919377/50000000000000 : ℝ)*(upper3) + (8604369/20000000000000 : ℝ)*(lower4) + (2053583/2500000000000 : ℝ)*(upper5) + (2089224863840813/50000000000000 : ℝ)*(major0) + (2089224863840813/50000000000000 : ℝ)*(major1) + (2089224863840813/50000000000000 : ℝ)*(major2) + (1805980943/25000000000000 : ℝ)*(sp2) + (1119080438011837/20000000000000 : ℝ)*(sp4) + (223816085357463/4000000000000 : ℝ)*(sp5) + (5595394550470327/100000000000000 : ℝ)*(sp6) + (2761497078204863/100000000000000 : ℝ)*(sp7) + (2761497078204863/100000000000000 : ℝ)*(f.failure) + (1119080438011837/20000000000000 : ℝ)*(f.sum) + (46181911877259/8455000000000000000000000000 : ℝ)*base65 + (7711682562557815487/845500000000000000000000000000000 : ℝ)*base67 + (14233100146566315487/845500000000000000000000000000000 : ℝ)*base69 + (9942871555451815487/845500000000000000000000000000000 : ℝ)*base71 + (6191419452593/1056875000000000000000000000 : ℝ)*base73 + (1956620665146184513/845500000000000000000000000000000 : ℝ)*base76 + (15023747103018315487/845500000000000000000000000000000 : ℝ)*base77 + (4453434133803684513/845500000000000000000000000000000 : ℝ)*base80 + (3147273719481/2113750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9006423/1250000000000000000000 : ℝ)*base90 + (9006423/1250000000000000000000 : ℝ)*base92 + (9006423/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1236_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1236_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1236_s4_0 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122162859/10000000000 : ℝ)*x 0 + (337358397/625000000 : ℝ)*x 1 + (2630540131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122162859/10000000000 : ℝ)^8429 ≤ (100808339757/781250000000 : ℝ)^6381 := by
    have hnat : (2122162859 : ℕ)^8429*781250000000^6381 ≤ 100808339757^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122162859 10000000000 100808339757 781250000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337358397/625000000 : ℝ)^8429 ≤ (5535719115857/12500000000000 : ℝ)^6381 := by
    have hnat : (337358397 : ℕ)^8429*12500000000000^6381 ≤ 5535719115857^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337358397 625000000 5535719115857 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630540131/5000000000 : ℝ)^8429 ≤ (8562155914633/20000000000000 : ℝ)^6381 := by
    have hnat : (2630540131 : ℕ)^8429*20000000000000^6381 ≤ 8562155914633^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630540131 5000000000 8562155914633 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122162859/10000000000 : ℝ), (337358397/625000000 : ℝ), (2630540131/5000000000 : ℝ)] ![(100808339757/781250000000 : ℝ), (5535719115857/12500000000000 : ℝ), (8562155914633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122162859/10000000000 : ℝ)|^8429 ≤ (100808339757/781250000000 : ℝ)^6381
        have hw : |(-2122162859/10000000000 : ℝ)|=(2122162859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337358397/625000000 : ℝ)|^8429 ≤ (5535719115857/12500000000000 : ℝ)^6381
        have hw : |(337358397/625000000 : ℝ)|=(337358397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630540131/5000000000 : ℝ)|^8429 ≤ (8562155914633/20000000000000 : ℝ)^6381
        have hw : |(2630540131/5000000000 : ℝ)|=(2630540131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_1 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345965567/10000000000 : ℝ)*x 0 + (-1095773981/5000000000 : ℝ)*x 1 + (2630540129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345965567/10000000000 : ℝ)^8429 ≤ (21862780136601/50000000000000 : ℝ)^6381 := by
    have hnat : (5345965567 : ℕ)^8429*50000000000000^6381 ≤ 21862780136601^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345965567 10000000000 21862780136601 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095773981/5000000000 : ℝ)^8429 ≤ (6731830091641/50000000000000 : ℝ)^6381 := by
    have hnat : (1095773981 : ℕ)^8429*50000000000000^6381 ≤ 6731830091641^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095773981 5000000000 6731830091641 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630540129/5000000000 : ℝ)^8429 ≤ (42810779530169/100000000000000 : ℝ)^6381 := by
    have hnat : (2630540129 : ℕ)^8429*100000000000000^6381 ≤ 42810779530169^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630540129 5000000000 42810779530169 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345965567/10000000000 : ℝ), (-1095773981/5000000000 : ℝ), (2630540129/5000000000 : ℝ)] ![(21862780136601/50000000000000 : ℝ), (6731830091641/50000000000000 : ℝ), (42810779530169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345965567/10000000000 : ℝ)|^8429 ≤ (21862780136601/50000000000000 : ℝ)^6381
        have hw : |(5345965567/10000000000 : ℝ)|=(5345965567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095773981/5000000000 : ℝ)|^8429 ≤ (6731830091641/50000000000000 : ℝ)^6381
        have hw : |(-1095773981/5000000000 : ℝ)|=(1095773981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630540129/5000000000 : ℝ)|^8429 ≤ (42810779530169/100000000000000 : ℝ)^6381
        have hw : |(2630540129/5000000000 : ℝ)|=(2630540129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_2 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345965571/10000000000 : ℝ)*x 0 + (5261080279/10000000000 : ℝ)*x 1 + (-2191547929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345965571/10000000000 : ℝ)^8429 ≤ (43725560316419/100000000000000 : ℝ)^6381 := by
    have hnat : (5345965571 : ℕ)^8429*100000000000000^6381 ≤ 43725560316419^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345965571 10000000000 43725560316419 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261080279/10000000000 : ℝ)^8429 ≤ (42810779755897/100000000000000 : ℝ)^6381 := by
    have hnat : (5261080279 : ℕ)^8429*100000000000000^6381 ≤ 42810779755897^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261080279 10000000000 42810779755897 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191547929/10000000000 : ℝ)^8429 ≤ (336591497887/2500000000000 : ℝ)^6381 := by
    have hnat : (2191547929 : ℕ)^8429*2500000000000^6381 ≤ 336591497887^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191547929 10000000000 336591497887 2500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345965571/10000000000 : ℝ), (5261080279/10000000000 : ℝ), (-2191547929/10000000000 : ℝ)] ![(43725560316419/100000000000000 : ℝ), (42810779755897/100000000000000 : ℝ), (336591497887/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345965571/10000000000 : ℝ)|^8429 ≤ (43725560316419/100000000000000 : ℝ)^6381
        have hw : |(5345965571/10000000000 : ℝ)|=(5345965571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261080279/10000000000 : ℝ)|^8429 ≤ (42810779755897/100000000000000 : ℝ)^6381
        have hw : |(5261080279/10000000000 : ℝ)|=(5261080279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191547929/10000000000 : ℝ)|^8429 ≤ (336591497887/2500000000000 : ℝ)^6381
        have hw : |(-2191547929/10000000000 : ℝ)|=(2191547929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_3 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175632823/5000000000 : ℝ)*x 0 + (1053740959/2500000000 : ℝ)*x 1 + (898371027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175632823/5000000000 : ℝ)^8429 ≤ (33314112791663/100000000000000 : ℝ)^6381 := by
    have hnat : (2175632823 : ℕ)^8429*100000000000000^6381 ≤ 33314112791663^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175632823 5000000000 33314112791663 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053740959/2500000000 : ℝ)^8429 ≤ (1996413030441/6250000000000 : ℝ)^6381 := by
    have hnat : (1053740959 : ℕ)^8429*6250000000000^6381 ≤ 1996413030441^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053740959 2500000000 1996413030441 6250000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898371027/2000000000 : ℝ)^8429 ≤ (8685819675031/25000000000000 : ℝ)^6381 := by
    have hnat : (898371027 : ℕ)^8429*25000000000000^6381 ≤ 8685819675031^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898371027 2000000000 8685819675031 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175632823/5000000000 : ℝ), (1053740959/2500000000 : ℝ), (898371027/2000000000 : ℝ)] ![(33314112791663/100000000000000 : ℝ), (1996413030441/6250000000000 : ℝ), (8685819675031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175632823/5000000000 : ℝ)|^8429 ≤ (33314112791663/100000000000000 : ℝ)^6381
        have hw : |(2175632823/5000000000 : ℝ)|=(2175632823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053740959/2500000000 : ℝ)|^8429 ≤ (1996413030441/6250000000000 : ℝ)^6381
        have hw : |(1053740959/2500000000 : ℝ)|=(1053740959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898371027/2000000000 : ℝ)|^8429 ≤ (8685819675031/25000000000000 : ℝ)^6381
        have hw : |(898371027/2000000000 : ℝ)|=(898371027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_4 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122169159/10000000000 : ℝ)*x 0 + (5261459183/10000000000 : ℝ)*x 1 + (2698676929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122169159/10000000000 : ℝ)^8429 ≤ (1290351808951/10000000000000 : ℝ)^6381 := by
    have hnat : (2122169159 : ℕ)^8429*10000000000000^6381 ≤ 1290351808951^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122169159 10000000000 1290351808951 10000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261459183/10000000000 : ℝ)^8429 ≤ (42814852618203/100000000000000 : ℝ)^6381 := by
    have hnat : (5261459183 : ℕ)^8429*100000000000000^6381 ≤ 42814852618203^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261459183 10000000000 42814852618203 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698676929/5000000000 : ℝ)^8429 ≤ (44281629267951/100000000000000 : ℝ)^6381 := by
    have hnat : (2698676929 : ℕ)^8429*100000000000000^6381 ≤ 44281629267951^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698676929 5000000000 44281629267951 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122169159/10000000000 : ℝ), (5261459183/10000000000 : ℝ), (2698676929/5000000000 : ℝ)] ![(1290351808951/10000000000000 : ℝ), (42814852618203/100000000000000 : ℝ), (44281629267951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122169159/10000000000 : ℝ)|^8429 ≤ (1290351808951/10000000000000 : ℝ)^6381
        have hw : |(-2122169159/10000000000 : ℝ)|=(2122169159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261459183/10000000000 : ℝ)|^8429 ≤ (42814852618203/100000000000000 : ℝ)^6381
        have hw : |(5261459183/10000000000 : ℝ)|=(5261459183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698676929/5000000000 : ℝ)|^8429 ≤ (44281629267951/100000000000000 : ℝ)^6381
        have hw : |(2698676929/5000000000 : ℝ)|=(2698676929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_5 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311113609/10000000000 : ℝ)*x 0 + (-411054859/2000000000 : ℝ)*x 1 + (1349338477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311113609/10000000000 : ℝ)^8429 ≤ (2167470193899/5000000000000 : ℝ)^6381 := by
    have hnat : (5311113609 : ℕ)^8429*5000000000000^6381 ≤ 2167470193899^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311113609 10000000000 2167470193899 5000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411054859/2000000000 : ℝ)^8429 ≤ (12368966298989/100000000000000 : ℝ)^6381 := by
    have hnat : (411054859 : ℕ)^8429*100000000000000^6381 ≤ 12368966298989^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411054859 2000000000 12368966298989 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349338477/2500000000 : ℝ)^8429 ≤ (44281629809827/100000000000000 : ℝ)^6381 := by
    have hnat : (1349338477 : ℕ)^8429*100000000000000^6381 ≤ 44281629809827^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349338477 2500000000 44281629809827 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311113609/10000000000 : ℝ), (-411054859/2000000000 : ℝ), (1349338477/2500000000 : ℝ)] ![(2167470193899/5000000000000 : ℝ), (12368966298989/100000000000000 : ℝ), (44281629809827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311113609/10000000000 : ℝ)|^8429 ≤ (2167470193899/5000000000000 : ℝ)^6381
        have hw : |(5311113609/10000000000 : ℝ)|=(5311113609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411054859/2000000000 : ℝ)|^8429 ≤ (12368966298989/100000000000000 : ℝ)^6381
        have hw : |(-411054859/2000000000 : ℝ)|=(411054859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349338477/2500000000 : ℝ)|^8429 ≤ (44281629809827/100000000000000 : ℝ)^6381
        have hw : |(1349338477/2500000000 : ℝ)|=(1349338477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_6 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327778417/2500000000 : ℝ)*x 0 + (337334613/625000000 : ℝ)*x 1 + (-2055274351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327778417/2500000000 : ℝ)^8429 ≤ (43349404514097/100000000000000 : ℝ)^6381 := by
    have hnat : (1327778417 : ℕ)^8429*100000000000000^6381 ≤ 43349404514097^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327778417 2500000000 43349404514097 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337334613/625000000 : ℝ)^8429 ≤ (1771265149043/4000000000000 : ℝ)^6381 := by
    have hnat : (337334613 : ℕ)^8429*4000000000000^6381 ≤ 1771265149043^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337334613 625000000 1771265149043 4000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055274351/10000000000 : ℝ)^8429 ≤ (3092241686043/25000000000000 : ℝ)^6381 := by
    have hnat : (2055274351 : ℕ)^8429*25000000000000^6381 ≤ 3092241686043^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055274351 10000000000 3092241686043 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327778417/2500000000 : ℝ), (337334613/625000000 : ℝ), (-2055274351/10000000000 : ℝ)] ![(43349404514097/100000000000000 : ℝ), (1771265149043/4000000000000 : ℝ), (3092241686043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327778417/2500000000 : ℝ)|^8429 ≤ (43349404514097/100000000000000 : ℝ)^6381
        have hw : |(1327778417/2500000000 : ℝ)|=(1327778417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337334613/625000000 : ℝ)|^8429 ≤ (1771265149043/4000000000000 : ℝ)^6381
        have hw : |(337334613/625000000 : ℝ)|=(337334613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055274351/10000000000 : ℝ)|^8429 ≤ (3092241686043/25000000000000 : ℝ)^6381
        have hw : |(-2055274351/10000000000 : ℝ)|=(2055274351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s4_7 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351278261/10000000000 : ℝ)*x 0 + (2245543609/5000000000 : ℝ)*x 1 + (526966851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351278261/10000000000 : ℝ)^8429 ≤ (33314240373079/100000000000000 : ℝ)^6381 := by
    have hnat : (4351278261 : ℕ)^8429*100000000000000^6381 ≤ 33314240373079^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351278261 10000000000 33314240373079 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245543609/5000000000 : ℝ)^8429 ≤ (6947086589053/20000000000000 : ℝ)^6381 := by
    have hnat : (2245543609 : ℕ)^8429*20000000000000^6381 ≤ 6947086589053^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245543609 5000000000 6947086589053 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526966851/1250000000 : ℝ)^8429 ≤ (15975163336061/50000000000000 : ℝ)^6381 := by
    have hnat : (526966851 : ℕ)^8429*50000000000000^6381 ≤ 15975163336061^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526966851 1250000000 15975163336061 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351278261/10000000000 : ℝ), (2245543609/5000000000 : ℝ), (526966851/1250000000 : ℝ)] ![(33314240373079/100000000000000 : ℝ), (6947086589053/20000000000000 : ℝ), (15975163336061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351278261/10000000000 : ℝ)|^8429 ≤ (33314240373079/100000000000000 : ℝ)^6381
        have hw : |(4351278261/10000000000 : ℝ)|=(4351278261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245543609/5000000000 : ℝ)|^8429 ≤ (6947086589053/20000000000000 : ℝ)^6381
        have hw : |(2245543609/5000000000 : ℝ)|=(2245543609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526966851/1250000000 : ℝ)|^8429 ≤ (15975163336061/50000000000000 : ℝ)^6381
        have hw : |(526966851/1250000000 : ℝ)|=(526966851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1236_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5671/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/6250 : ℝ) ^ (2107/512 : ℝ) ≤ (2183526410800857/20000000000000000000 : ℝ) := by
    have hpowers : (681/6250 : ℝ)^2107 ≤ (2183526410800857/20000000000000000000 : ℝ)^512 := by
      have hnat : (681 : ℕ)^2107*20000000000000000000^512 ≤ 2183526410800857^512*6250^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 6250 2183526410800857 20000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/6250 : ℝ)) (X := (2183526410800857/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (2107/512 : ℝ) ≤ (9375296497226891/25000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^2107 ≤ (9375296497226891/25000000000000000000 : ℝ)^512 := by
      have hnat : (7353 : ℕ)^2107*25000000000000000000^512 ≤ 9375296497226891^512*50000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 9375296497226891 25000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (9375296497226891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002183526410800857/10000000000000000000 : ℝ) ≤ (2000106110407041/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (10002183526410800857/10000000000000000000 : ℝ)^512 ≤ (2000106110407041/2000000000000000 : ℝ)^2107 := by
      have hnat : (10002183526410800857 : ℕ)^512*2000000000000000^2107 ≤ 2000106110407041^2107*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002183526410800857 10000000000000000000 2000106110407041 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000106110407041/2000000000000000 : ℝ)) (X := (10002183526410800857/10000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048418818042911849/100000000000000000000 : ℝ) ≤ (2000235271883231/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (100048418818042911849/100000000000000000000 : ℝ)^512 ≤ (2000235271883231/2000000000000000 : ℝ)^2107 := by
      have hnat : (100048418818042911849 : ℕ)^512*2000000000000000^2107 ≤ 2000235271883231^2107*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048418818042911849 100000000000000000000 2000235271883231 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000235271883231/2000000000000000 : ℝ)) (X := (100048418818042911849/100000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509375296497226891/12500000000000000000 : ℝ) ≤ (2000364433359421/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (12509375296497226891/12500000000000000000 : ℝ)^512 ≤ (2000364433359421/2000000000000000 : ℝ)^2107 := by
      have hnat : (12509375296497226891 : ℕ)^512*2000000000000000^2107 ≤ 2000364433359421^2107*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509375296497226891 12500000000000000000 2000364433359421 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000364433359421/2000000000000000 : ℝ)) (X := (12509375296497226891/12500000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2183526410800857/20000000000000000000 : ℝ) ≤ ((253919653125389791/254000000000000000 : ℝ)+2*(12916147619/7620000000000 : ℝ)*(681/6250 : ℝ))^(2107/512 : ℝ) := by
    rw [show (253919653125389791/254000000000000000 : ℝ)+2*(12916147619/7620000000000 : ℝ)*(681/6250 : ℝ)=(2000106110407041/2000000000000000 : ℝ) by norm_num, show 1+2*(2183526410800857/20000000000000000000 : ℝ)=(10002183526410800857/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9375296497226891/25000000000000000000 : ℝ)+(2183526410800857/20000000000000000000 : ℝ) ≤ ((253919653125389791/254000000000000000 : ℝ)+(12916147619/7620000000000 : ℝ)*((7353/50000 : ℝ)+(681/6250 : ℝ)))^(2107/512 : ℝ) := by
    rw [show (253919653125389791/254000000000000000 : ℝ)+(12916147619/7620000000000 : ℝ)*((7353/50000 : ℝ)+(681/6250 : ℝ))=(2000235271883231/2000000000000000 : ℝ) by norm_num, show 1+(9375296497226891/25000000000000000000 : ℝ)+(2183526410800857/20000000000000000000 : ℝ)=(100048418818042911849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9375296497226891/25000000000000000000 : ℝ) ≤ ((253919653125389791/254000000000000000 : ℝ)+2*(12916147619/7620000000000 : ℝ)*(7353/50000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (253919653125389791/254000000000000000 : ℝ)+2*(12916147619/7620000000000 : ℝ)*(7353/50000 : ℝ)=(2000364433359421/2000000000000000 : ℝ) by norm_num, show 1+2*(9375296497226891/25000000000000000000 : ℝ)=(12509375296497226891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (253919653125389791/254000000000000000 : ℝ)*(X 1 0+X 2 0)+(12916147619/7620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (253919653125389791/254000000000000000 : ℝ)) (alpha := (12916147619/7620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (253919653125389791/254000000000000000 : ℝ)*(X 0 1+X 2 1)+(12916147619/7620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (253919653125389791/254000000000000000 : ℝ)) (alpha := (12916147619/7620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (253919653125389791/254000000000000000 : ℝ)*(X 0 2+X 1 2)+(12916147619/7620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (253919653125389791/254000000000000000 : ℝ)) (alpha := (12916147619/7620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122162859/10000000000 : ℝ)*X 0 0+(337358397/625000000 : ℝ)*X 0 1+(2630540131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345965567/10000000000 : ℝ)*X 1 0+(-1095773981/5000000000 : ℝ)*X 1 1+(2630540129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345965571/10000000000 : ℝ)*X 2 0+(5261080279/10000000000 : ℝ)*X 2 1+(-2191547929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175632823/5000000000 : ℝ)*X 0 0+(1053740959/2500000000 : ℝ)*X 0 1+(898371027/2000000000 : ℝ)*X 0 2+(2175632823/5000000000 : ℝ)*X 1 0+(1053740959/2500000000 : ℝ)*X 1 1+(898371027/2000000000 : ℝ)*X 1 2+(2175632823/5000000000 : ℝ)*X 2 0+(1053740959/2500000000 : ℝ)*X 2 1+(898371027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122169159/10000000000 : ℝ)*X 0 0+(5261459183/10000000000 : ℝ)*X 0 1+(2698676929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311113609/10000000000 : ℝ)*X 1 0+(-411054859/2000000000 : ℝ)*X 1 1+(1349338477/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327778417/2500000000 : ℝ)*X 2 0+(337334613/625000000 : ℝ)*X 2 1+(-2055274351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351278261/10000000000 : ℝ)*X 0 0+(2245543609/5000000000 : ℝ)*X 0 1+(526966851/1250000000 : ℝ)*X 0 2+(4351278261/10000000000 : ℝ)*X 1 0+(2245543609/5000000000 : ℝ)*X 1 1+(526966851/1250000000 : ℝ)*X 1 2+(4351278261/10000000000 : ℝ)*X 2 0+(2245543609/5000000000 : ℝ)*X 2 1+(526966851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (817726655268716485513/127000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306997201/25000000000000 : ℝ)*(base19) + (561834907/50000000000000 : ℝ)*(base23) + (586957/1000000000000 : ℝ)*(lower2) + (27145447/20000000000000 : ℝ)*(upper3) + (104791551/100000000000000 : ℝ)*(upper5) + (5464684248526683/100000000000000 : ℝ)*(major0) + (5464684248526683/100000000000000 : ℝ)*(major1) + (1366171062131671/25000000000000 : ℝ)*(major2) + (22868058439161/312500000000 : ℝ)*(sp0) + (7317810001197837/100000000000000 : ℝ)*(sp1) + (7317810105516827/100000000000000 : ℝ)*(sp2) + (1805770336297053/50000000000000 : ℝ)*(sp3) + (32528655121/100000000000000 : ℝ)*(sp4) + (16380646191/100000000000000 : ℝ)*(sp7) + (3611557053240297/100000000000000 : ℝ)*(f.failure) + (7317811229186641/100000000000000 : ℝ)*(f.sum) + (516026938277/762000000000000000000000000 : ℝ)*base65 + (755778503158079759/76200000000000000000000000000000 : ℝ)*base67 + (66081514946954239/6350000000000000000000000000000 : ℝ)*base70 + (1098401923779720241/76200000000000000000000000000000 : ℝ)*base72 + (4701790739453/762000000000000000000000000 : ℝ)*base73 + (29604495814245761/6350000000000000000000000000000 : ℝ)*base75 + (422199857347593253/25400000000000000000000000000000 : ℝ)*base77 + (115385870704606747/25400000000000000000000000000000 : ℝ)*base80 + (448131664413/63500000000000000000000000 : ℝ)*base82 + (2117937/1250000000000000000000 : ℝ)*base90 + (2117937/1250000000000000000000 : ℝ)*base92 + (14617937/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (343778122613462216151/127000000000000000000000000 : ℝ) := by norm_num
    linear_combination (679080983/100000000000000 : ℝ)*(base19) + (777517317/100000000000000 : ℝ)*(base23) + (22174537/100000000000000 : ℝ)*(upper2) + (46062763/100000000000000 : ℝ)*(upper3) + (106520733/100000000000000 : ℝ)*(upper5) + (1099035142097619/20000000000000 : ℝ)*(major0) + (1099035142097619/20000000000000 : ℝ)*(major1) + (1099035142097619/20000000000000 : ℝ)*(major2) + (2225576201/10000000000000 : ℝ)*(sp1) + (2304602199/12500000000000 : ℝ)*(sp2) + (3679321382359271/50000000000000 : ℝ)*(sp4) + (1839654957468887/25000000000000 : ℝ)*(sp5) + (459913971898977/6250000000000 : ℝ)*(sp6) + (1815854283013579/50000000000000 : ℝ)*(sp7) + (1815854283013579/50000000000000 : ℝ)*(f.failure) + (3679321382359271/50000000000000 : ℝ)*(f.sum) + (40904388463/25400000000000000000000000 : ℝ)*base65 + (18495799773692371/5080000000000000000000000000000 : ℝ)*base68 + (36972653830707629/5080000000000000000000000000000 : ℝ)*base69 + (19186258184492371/5080000000000000000000000000000 : ℝ)*base72 + (191151396893/127000000000000000000000000 : ℝ)*base74 + (27853252219532371/5080000000000000000000000000000 : ℝ)*base76 + (33483360601027629/5080000000000000000000000000000 : ℝ)*base77 + (105398960625267629/5080000000000000000000000000000 : ℝ)*base79 + (521696847207/127000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5187059/625000000000000000000 : ℝ)*base90 + (5187059/625000000000000000000 : ℝ)*base92 + (5187059/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1236_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1236_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1236_s5_0 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122622717/10000000000 : ℝ)*x 0 + (5392550887/10000000000 : ℝ)*x 1 + (5265961403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122622717/10000000000 : ℝ)^8429 ≤ (1613395140383/12500000000000 : ℝ)^6381 := by
    have hnat : (2122622717 : ℕ)^8429*12500000000000^6381 ≤ 1613395140383^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122622717 10000000000 1613395140383 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392550887/10000000000 : ℝ)^8429 ≤ (44229584396833/100000000000000 : ℝ)^6381 := by
    have hnat : (5392550887 : ℕ)^8429*100000000000000^6381 ≤ 44229584396833^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392550887 10000000000 44229584396833 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265961403/10000000000 : ℝ)^8429 ≤ (8572650892077/20000000000000 : ℝ)^6381 := by
    have hnat : (5265961403 : ℕ)^8429*20000000000000^6381 ≤ 8572650892077^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265961403 10000000000 8572650892077 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122622717/10000000000 : ℝ), (5392550887/10000000000 : ℝ), (5265961403/10000000000 : ℝ)] ![(1613395140383/12500000000000 : ℝ), (44229584396833/100000000000000 : ℝ), (8572650892077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122622717/10000000000 : ℝ)|^8429 ≤ (1613395140383/12500000000000 : ℝ)^6381
        have hw : |(-2122622717/10000000000 : ℝ)|=(2122622717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392550887/10000000000 : ℝ)|^8429 ≤ (44229584396833/100000000000000 : ℝ)^6381
        have hw : |(5392550887/10000000000 : ℝ)|=(5392550887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265961403/10000000000 : ℝ)|^8429 ≤ (8572650892077/20000000000000 : ℝ)^6381
        have hw : |(5265961403/10000000000 : ℝ)|=(5265961403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_1 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344654557/10000000000 : ℝ)*x 0 + (-136676593/625000000 : ℝ)*x 1 + (526596137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344654557/10000000000 : ℝ)^8429 ≤ (10927849072143/25000000000000 : ℝ)^6381 := by
    have hnat : (5344654557 : ℕ)^8429*25000000000000^6381 ≤ 10927849072143^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344654557 10000000000 10927849072143 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136676593/625000000 : ℝ)^8429 ≤ (1678168699971/12500000000000 : ℝ)^6381 := by
    have hnat : (136676593 : ℕ)^8429*12500000000000^6381 ≤ 1678168699971^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136676593 625000000 1678168699971 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526596137/1000000000 : ℝ)^8429 ≤ (8572650821113/20000000000000 : ℝ)^6381 := by
    have hnat : (526596137 : ℕ)^8429*20000000000000^6381 ≤ 8572650821113^6381*1000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526596137 1000000000 8572650821113 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344654557/10000000000 : ℝ), (-136676593/625000000 : ℝ), (526596137/1000000000 : ℝ)] ![(10927849072143/25000000000000 : ℝ), (1678168699971/12500000000000 : ℝ), (8572650821113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344654557/10000000000 : ℝ)|^8429 ≤ (10927849072143/25000000000000 : ℝ)^6381
        have hw : |(5344654557/10000000000 : ℝ)|=(5344654557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136676593/625000000 : ℝ)|^8429 ≤ (1678168699971/12500000000000 : ℝ)^6381
        have hw : |(-136676593/625000000 : ℝ)|=(136676593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526596137/1000000000 : ℝ)|^8429 ≤ (8572650821113/20000000000000 : ℝ)^6381
        have hw : |(526596137/1000000000 : ℝ)|=(526596137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_2 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068930879/2000000000 : ℝ)*x 0 + (5265961333/10000000000 : ℝ)*x 1 + (-2186825751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068930879/2000000000 : ℝ)^8429 ≤ (21855697269207/50000000000000 : ℝ)^6381 := by
    have hnat : (1068930879 : ℕ)^8429*50000000000000^6381 ≤ 21855697269207^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068930879 2000000000 21855697269207 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265961333/10000000000 : ℝ)^8429 ≤ (8572650741547/20000000000000 : ℝ)^6381 := by
    have hnat : (5265961333 : ℕ)^8429*20000000000000^6381 ≤ 8572650741547^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265961333 10000000000 8572650741547 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186825751/10000000000 : ℝ)^8429 ≤ (13425351732589/100000000000000 : ℝ)^6381 := by
    have hnat : (2186825751 : ℕ)^8429*100000000000000^6381 ≤ 13425351732589^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186825751 10000000000 13425351732589 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068930879/2000000000 : ℝ), (5265961333/10000000000 : ℝ), (-2186825751/10000000000 : ℝ)] ![(21855697269207/50000000000000 : ℝ), (8572650741547/20000000000000 : ℝ), (13425351732589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068930879/2000000000 : ℝ)|^8429 ≤ (21855697269207/50000000000000 : ℝ)^6381
        have hw : |(1068930879/2000000000 : ℝ)|=(1068930879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265961333/10000000000 : ℝ)|^8429 ≤ (8572650741547/20000000000000 : ℝ)^6381
        have hw : |(5265961333/10000000000 : ℝ)|=(5265961333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186825751/10000000000 : ℝ)|^8429 ≤ (13425351732589/100000000000000 : ℝ)^6381
        have hw : |(-2186825751/10000000000 : ℝ)|=(2186825751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_3 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175767587/5000000000 : ℝ)*x 0 + (528140687/1250000000 : ℝ)*x 1 + (4481624493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175767587/5000000000 : ℝ)^8429 ≤ (33316838680673/100000000000000 : ℝ)^6381 := by
    have hnat : (2175767587 : ℕ)^8429*100000000000000^6381 ≤ 33316838680673^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175767587 5000000000 33316838680673 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528140687/1250000000 : ℝ)^8429 ≤ (32044373008033/100000000000000 : ℝ)^6381 := by
    have hnat : (528140687 : ℕ)^8429*100000000000000^6381 ≤ 32044373008033^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528140687 1250000000 32044373008033 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481624493/10000000000 : ℝ)^8429 ≤ (17319394147917/50000000000000 : ℝ)^6381 := by
    have hnat : (4481624493 : ℕ)^8429*50000000000000^6381 ≤ 17319394147917^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481624493 10000000000 17319394147917 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175767587/5000000000 : ℝ), (528140687/1250000000 : ℝ), (4481624493/10000000000 : ℝ)] ![(33316838680673/100000000000000 : ℝ), (32044373008033/100000000000000 : ℝ), (17319394147917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175767587/5000000000 : ℝ)|^8429 ≤ (33316838680673/100000000000000 : ℝ)^6381
        have hw : |(2175767587/5000000000 : ℝ)|=(2175767587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528140687/1250000000 : ℝ)|^8429 ≤ (32044373008033/100000000000000 : ℝ)^6381
        have hw : |(528140687/1250000000 : ℝ)|=(528140687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481624493/10000000000 : ℝ)|^8429 ≤ (17319394147917/50000000000000 : ℝ)^6381
        have hw : |(4481624493/10000000000 : ℝ)|=(4481624493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_4 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122628411/10000000000 : ℝ)*x 0 + (5266286109/10000000000 : ℝ)*x 1 + (269611221/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122628411/10000000000 : ℝ)^8429 ≤ (322680171489/2500000000000 : ℝ)^6381 := by
    have hnat : (2122628411 : ℕ)^8429*2500000000000^6381 ≤ 322680171489^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122628411 10000000000 322680171489 2500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266286109/10000000000 : ℝ)^8429 ≤ (42866745778253/100000000000000 : ℝ)^6381 := by
    have hnat : (5266286109 : ℕ)^8429*100000000000000^6381 ≤ 42866745778253^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266286109 10000000000 42866745778253 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269611221/500000000 : ℝ)^8429 ≤ (22113023674289/50000000000000 : ℝ)^6381 := by
    have hnat : (269611221 : ℕ)^8429*50000000000000^6381 ≤ 22113023674289^6381*500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269611221 500000000 22113023674289 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122628411/10000000000 : ℝ), (5266286109/10000000000 : ℝ), (269611221/500000000 : ℝ)] ![(322680171489/2500000000000 : ℝ), (42866745778253/100000000000000 : ℝ), (22113023674289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122628411/10000000000 : ℝ)|^8429 ≤ (322680171489/2500000000000 : ℝ)^6381
        have hw : |(-2122628411/10000000000 : ℝ)|=(2122628411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266286109/10000000000 : ℝ)|^8429 ≤ (42866745778253/100000000000000 : ℝ)^6381
        have hw : |(5266286109/10000000000 : ℝ)|=(5266286109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269611221/500000000 : ℝ)|^8429 ≤ (22113023674289/50000000000000 : ℝ)^6381
        have hw : |(269611221/500000000 : ℝ)|=(269611221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_5 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41502879/78125000 : ℝ)*x 0 + (-2060562459/10000000000 : ℝ)*x 1 + (539222399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41502879/78125000 : ℝ)^8429 ≤ (21681467151999/50000000000000 : ℝ)^6381 := by
    have hnat : (41502879 : ℕ)^8429*50000000000000^6381 ≤ 21681467151999^6381*78125000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41502879 78125000 21681467151999 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060562459/10000000000 : ℝ)^8429 ≤ (12411022982243/100000000000000 : ℝ)^6381 := by
    have hnat : (2060562459 : ℕ)^8429*100000000000000^6381 ≤ 12411022982243^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060562459 10000000000 12411022982243 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539222399/1000000000 : ℝ)^8429 ≤ (8845208537973/20000000000000 : ℝ)^6381 := by
    have hnat : (539222399 : ℕ)^8429*20000000000000^6381 ≤ 8845208537973^6381*1000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539222399 1000000000 8845208537973 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41502879/78125000 : ℝ), (-2060562459/10000000000 : ℝ), (539222399/1000000000 : ℝ)] ![(21681467151999/50000000000000 : ℝ), (12411022982243/100000000000000 : ℝ), (8845208537973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41502879/78125000 : ℝ)|^8429 ≤ (21681467151999/50000000000000 : ℝ)^6381
        have hw : |(41502879/78125000 : ℝ)|=(41502879/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060562459/10000000000 : ℝ)|^8429 ≤ (12411022982243/100000000000000 : ℝ)^6381
        have hw : |(-2060562459/10000000000 : ℝ)|=(2060562459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539222399/1000000000 : ℝ)|^8429 ≤ (8845208537973/20000000000000 : ℝ)^6381
        have hw : |(539222399/1000000000 : ℝ)|=(539222399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_6 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332023033/625000000 : ℝ)*x 0 + (5392223929/10000000000 : ℝ)*x 1 + (-1030281261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332023033/625000000 : ℝ)^8429 ≤ (43362934476517/100000000000000 : ℝ)^6381 := by
    have hnat : (332023033 : ℕ)^8429*100000000000000^6381 ≤ 43362934476517^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332023033 625000000 43362934476517 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392223929/10000000000 : ℝ)^8429 ≤ (22113021014489/50000000000000 : ℝ)^6381 := by
    have hnat : (5392223929 : ℕ)^8429*50000000000000^6381 ≤ 22113021014489^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392223929 10000000000 22113021014489 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030281261/5000000000 : ℝ)^8429 ≤ (387844483859/3125000000000 : ℝ)^6381 := by
    have hnat : (1030281261 : ℕ)^8429*3125000000000^6381 ≤ 387844483859^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030281261 5000000000 387844483859 3125000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332023033/625000000 : ℝ), (5392223929/10000000000 : ℝ), (-1030281261/5000000000 : ℝ)] ![(43362934476517/100000000000000 : ℝ), (22113021014489/50000000000000 : ℝ), (387844483859/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332023033/625000000 : ℝ)|^8429 ≤ (43362934476517/100000000000000 : ℝ)^6381
        have hw : |(332023033/625000000 : ℝ)|=(332023033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392223929/10000000000 : ℝ)|^8429 ≤ (22113021014489/50000000000000 : ℝ)^6381
        have hw : |(5392223929/10000000000 : ℝ)|=(5392223929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030281261/5000000000 : ℝ)|^8429 ≤ (387844483859/3125000000000 : ℝ)^6381
        have hw : |(-1030281261/5000000000 : ℝ)|=(1030281261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_s5_7 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175772773/5000000000 : ℝ)*x 0 + (560120639/1250000000 : ℝ)*x 1 + (2112893483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175772773/5000000000 : ℝ)^8429 ≤ (16658471789827/50000000000000 : ℝ)^6381 := by
    have hnat : (2175772773 : ℕ)^8429*50000000000000^6381 ≤ 16658471789827^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175772773 5000000000 16658471789827 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560120639/1250000000 : ℝ)^8429 ≤ (6926411269699/20000000000000 : ℝ)^6381 := by
    have hnat : (560120639 : ℕ)^8429*20000000000000^6381 ≤ 6926411269699^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560120639 1250000000 6926411269699 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112893483/5000000000 : ℝ)^8429 ≤ (16025500031229/50000000000000 : ℝ)^6381 := by
    have hnat : (2112893483 : ℕ)^8429*50000000000000^6381 ≤ 16025500031229^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112893483 5000000000 16025500031229 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175772773/5000000000 : ℝ), (560120639/1250000000 : ℝ), (2112893483/5000000000 : ℝ)] ![(16658471789827/50000000000000 : ℝ), (6926411269699/20000000000000 : ℝ), (16025500031229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175772773/5000000000 : ℝ)|^8429 ≤ (16658471789827/50000000000000 : ℝ)^6381
        have hw : |(2175772773/5000000000 : ℝ)|=(2175772773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560120639/1250000000 : ℝ)|^8429 ≤ (6926411269699/20000000000000 : ℝ)^6381
        have hw : |(560120639/1250000000 : ℝ)|=(560120639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112893483/5000000000 : ℝ)|^8429 ≤ (16025500031229/50000000000000 : ℝ)^6381
        have hw : |(2112893483/5000000000 : ℝ)|=(2112893483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1236_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5723/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (883/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5671/50000 : ℝ) ^ (2107/512 : ℝ) ≤ (1287734477724961/10000000000000000000 : ℝ) := by
    have hpowers : (5671/50000 : ℝ)^2107 ≤ (1287734477724961/10000000000000000000 : ℝ)^512 := by
      have hnat : (5671 : ℕ)^2107*10000000000000000000^512 ≤ 1287734477724961^512*50000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5671 50000 1287734477724961 10000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5671/50000 : ℝ)) (X := (1287734477724961/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (2107/512 : ℝ) ≤ (4101126102243009/12500000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^2107 ≤ (4101126102243009/12500000000000000000 : ℝ)^512 := by
      have hnat : (3559 : ℕ)^2107*12500000000000000000^512 ≤ 4101126102243009^512*25000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 4101126102243009 12500000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (4101126102243009/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001287734477724961/5000000000000000000 : ℝ) ≤ (10000625776735397/10000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (5001287734477724961/5000000000000000000 : ℝ)^512 ≤ (10000625776735397/10000000000000000 : ℝ)^2107 := by
      have hnat : (5001287734477724961 : ℕ)^512*10000000000000000^2107 ≤ 10000625776735397^2107*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001287734477724961 5000000000000000000 10000625776735397 10000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000625776735397/10000000000000000 : ℝ)) (X := (5001287734477724961/5000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022843176797596841/50000000000000000000 : ℝ) ≤ (5000554992150223/5000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (50022843176797596841/50000000000000000000 : ℝ)^512 ≤ (5000554992150223/5000000000000000 : ℝ)^2107 := by
      have hnat : (50022843176797596841 : ℕ)^512*5000000000000000^2107 ≤ 5000554992150223^2107*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022843176797596841 50000000000000000000 5000554992150223 5000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000554992150223/5000000000000000 : ℝ)) (X := (50022843176797596841/50000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254101126102243009/6250000000000000000 : ℝ) ≤ (2000318838373099/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (6254101126102243009/6250000000000000000 : ℝ)^512 ≤ (2000318838373099/2000000000000000 : ℝ)^2107 := by
      have hnat : (6254101126102243009 : ℕ)^512*2000000000000000^2107 ≤ 2000318838373099^2107*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254101126102243009 6250000000000000000 2000318838373099 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000318838373099/2000000000000000 : ℝ)) (X := (6254101126102243009/6250000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1287734477724961/10000000000000000000 : ℝ) ≤ ((14465413616733333701/14470000000000000000 : ℝ)+2*(484207565049/289400000000000 : ℝ)*(5671/50000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (14465413616733333701/14470000000000000000 : ℝ)+2*(484207565049/289400000000000 : ℝ)*(5671/50000 : ℝ)=(10000625776735397/10000000000000000 : ℝ) by norm_num, show 1+2*(1287734477724961/10000000000000000000 : ℝ)=(5001287734477724961/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4101126102243009/12500000000000000000 : ℝ)+(1287734477724961/10000000000000000000 : ℝ) ≤ ((14465413616733333701/14470000000000000000 : ℝ)+(484207565049/289400000000000 : ℝ)*((3559/25000 : ℝ)+(5671/50000 : ℝ)))^(2107/512 : ℝ) := by
    rw [show (14465413616733333701/14470000000000000000 : ℝ)+(484207565049/289400000000000 : ℝ)*((3559/25000 : ℝ)+(5671/50000 : ℝ))=(5000554992150223/5000000000000000 : ℝ) by norm_num, show 1+(4101126102243009/12500000000000000000 : ℝ)+(1287734477724961/10000000000000000000 : ℝ)=(50022843176797596841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4101126102243009/12500000000000000000 : ℝ) ≤ ((14465413616733333701/14470000000000000000 : ℝ)+2*(484207565049/289400000000000 : ℝ)*(3559/25000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (14465413616733333701/14470000000000000000 : ℝ)+2*(484207565049/289400000000000 : ℝ)*(3559/25000 : ℝ)=(2000318838373099/2000000000000000 : ℝ) by norm_num, show 1+2*(4101126102243009/12500000000000000000 : ℝ)=(6254101126102243009/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14465413616733333701/14470000000000000000 : ℝ)*(X 1 0+X 2 0)+(484207565049/289400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14465413616733333701/14470000000000000000 : ℝ)) (alpha := (484207565049/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14465413616733333701/14470000000000000000 : ℝ)*(X 0 1+X 2 1)+(484207565049/289400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14465413616733333701/14470000000000000000 : ℝ)) (alpha := (484207565049/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14465413616733333701/14470000000000000000 : ℝ)*(X 0 2+X 1 2)+(484207565049/289400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (14465413616733333701/14470000000000000000 : ℝ)) (alpha := (484207565049/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122622717/10000000000 : ℝ)*X 0 0+(5392550887/10000000000 : ℝ)*X 0 1+(5265961403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344654557/10000000000 : ℝ)*X 1 0+(-136676593/625000000 : ℝ)*X 1 1+(526596137/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068930879/2000000000 : ℝ)*X 2 0+(5265961333/10000000000 : ℝ)*X 2 1+(-2186825751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175767587/5000000000 : ℝ)*X 0 0+(528140687/1250000000 : ℝ)*X 0 1+(4481624493/10000000000 : ℝ)*X 0 2+(2175767587/5000000000 : ℝ)*X 1 0+(528140687/1250000000 : ℝ)*X 1 1+(4481624493/10000000000 : ℝ)*X 1 2+(2175767587/5000000000 : ℝ)*X 2 0+(528140687/1250000000 : ℝ)*X 2 1+(4481624493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122628411/10000000000 : ℝ)*X 0 0+(5266286109/10000000000 : ℝ)*X 0 1+(269611221/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41502879/78125000 : ℝ)*X 1 0+(-2060562459/10000000000 : ℝ)*X 1 1+(539222399/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332023033/625000000 : ℝ)*X 2 0+(5392223929/10000000000 : ℝ)*X 2 1+(-1030281261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175772773/5000000000 : ℝ)*X 0 0+(560120639/1250000000 : ℝ)*X 0 1+(2112893483/5000000000 : ℝ)*X 0 2+(2175772773/5000000000 : ℝ)*X 1 0+(560120639/1250000000 : ℝ)*X 1 1+(2112893483/5000000000 : ℝ)*X 1 2+(2175772773/5000000000 : ℝ)*X 2 0+(560120639/1250000000 : ℝ)*X 2 1+(2112893483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4830591220005807888315710397/723500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7204121/625000000000 : ℝ)*(base19) + (35901453/3125000000000 : ℝ)*(base23) + (242592173/100000000000000 : ℝ)*(upper3) + (16485581/12500000000000 : ℝ)*(lower4) + (5899153092110249/100000000000000 : ℝ)*(major0) + (5899153092110249/100000000000000 : ℝ)*(major1) + (23596612368441/400000000000 : ℝ)*(major2) + (1974897676394541/25000000000000 : ℝ)*(sp0) + (987451436530097/12500000000000 : ℝ)*(sp1) + (789960965351811/10000000000000 : ℝ)*(sp2) + (243666927848783/6250000000000 : ℝ)*(sp3) + (21939321971/100000000000000 : ℝ)*(sp4) + (184253553/10000000000000 : ℝ)*(sp6) + (4494236643/20000000000000 : ℝ)*(sp7) + (121834166148867/3125000000000 : ℝ)*(f.failure) + (1579922528980027/20000000000000 : ℝ)*(f.sum) + (64646638498031/28940000000000000000000000000 : ℝ)*base65 + (9329880621513298451/1447000000000000000000000000000000 : ℝ)*base68 + (32454799016357659/5788000000000000000000000000000 : ℝ)*base70 + (413712058593701549/1447000000000000000000000000000000 : ℝ)*base71 + (152010545916251/28940000000000000000000000000 : ℝ)*base73 + (104587674976261659/5788000000000000000000000000000 : ℝ)*base76 + (1821191722584748451/1447000000000000000000000000000000 : ℝ)*base78 + (21931567937536748451/1447000000000000000000000000000000 : ℝ)*base80 + (75616263310921/14470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (102367/9765625000000000000 : ℝ)*base89 + (102367/9765625000000000000 : ℝ)*base91 + (18843/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (227772044756529484793601693/90437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3440936193/100000000000000 : ℝ)*(base19) + (2076896403/50000000000000 : ℝ)*(base23) + (353770189/100000000000000 : ℝ)*(upper2) + (69128751/25000000000000 : ℝ)*(upper3) + (545782903/100000000000000 : ℝ)*(upper5) + (1482402599702469/25000000000000 : ℝ)*(major0) + (1482402599702469/25000000000000 : ℝ)*(major1) + (1482402599702469/25000000000000 : ℝ)*(major2) + (15326059087/20000000000000 : ℝ)*(sp1) + (20103982349/25000000000000 : ℝ)*(sp2) + (1588079691399987/20000000000000 : ℝ)*(sp4) + (1985079596442077/25000000000000 : ℝ)*(sp5) + (7940313887277733/100000000000000 : ℝ)*(sp6) + (979705564166973/25000000000000 : ℝ)*(sp7) + (979705564166973/25000000000000 : ℝ)*(f.failure) + (1588079691399987/20000000000000 : ℝ)*(f.sum) + (16299612517583/7235000000000000000000000000 : ℝ)*base66 + (4582759325616407769/361750000000000000000000000000000 : ℝ)*base67 + (4884197803818657769/361750000000000000000000000000000 : ℝ)*base69 + (1204959504569407769/361750000000000000000000000000000 : ℝ)*base71 + (965818021871/3617500000000000000000000000 : ℝ)*base73 + (5632570948821157769/361750000000000000000000000000000 : ℝ)*base75 + (42975784053342231/361750000000000000000000000000000 : ℝ)*base78 + (6159586006923907769/361750000000000000000000000000000 : ℝ)*base79 + (6301548362697/1808750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (618267/312500000000000000000 : ℝ)*base89 + (618267/312500000000000000000 : ℝ)*base91 + (618267/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1236_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1236_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1236_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1236_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1236_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1236_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1236_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
