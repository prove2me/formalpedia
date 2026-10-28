-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:57:09.161427+00:00
-- url     : https://prove2.me/submissions/27327c4d-8c1c-4d32-9dfb-01baae65a5cc

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
theorem support_rectangle_w1053_s3_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205263893/10000000000 : ℝ)*x 0 + (5439067221/10000000000 : ℝ)*x 1 + (2611472551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205263893/10000000000 : ℝ)^4123 ≤ (13381992629117/100000000000000 : ℝ)^3099 := by
    have hnat : (2205263893 : ℕ)^4123*100000000000000^3099 ≤ 13381992629117^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205263893 10000000000 13381992629117 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439067221/10000000000 : ℝ)^4123 ≤ (5559605741647/12500000000000 : ℝ)^3099 := by
    have hnat : (5439067221 : ℕ)^4123*12500000000000^3099 ≤ 5559605741647^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439067221 10000000000 5559605741647 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611472551/5000000000 : ℝ)^4123 ≤ (8428232284963/20000000000000 : ℝ)^3099 := by
    have hnat : (2611472551 : ℕ)^4123*20000000000000^3099 ≤ 8428232284963^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611472551 5000000000 8428232284963 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205263893/10000000000 : ℝ), (5439067221/10000000000 : ℝ), (2611472551/5000000000 : ℝ)] ![(13381992629117/100000000000000 : ℝ), (5559605741647/12500000000000 : ℝ), (8428232284963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205263893/10000000000 : ℝ)|^4123 ≤ (13381992629117/100000000000000 : ℝ)^3099
        have hw : |(-2205263893/10000000000 : ℝ)|=(2205263893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439067221/10000000000 : ℝ)|^4123 ≤ (5559605741647/12500000000000 : ℝ)^3099
        have hw : |(5439067221/10000000000 : ℝ)|=(5439067221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611472551/5000000000 : ℝ)|^4123 ≤ (8428232284963/20000000000000 : ℝ)^3099
        have hw : |(2611472551/5000000000 : ℝ)|=(2611472551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071205769/2000000000 : ℝ)*x 0 + (-2315972201/10000000000 : ℝ)*x 1 + (2611472491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071205769/2000000000 : ℝ)^4123 ≤ (43575732269929/100000000000000 : ℝ)^3099 := by
    have hnat : (1071205769 : ℕ)^4123*100000000000000^3099 ≤ 43575732269929^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071205769 2000000000 43575732269929 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2315972201/10000000000 : ℝ)^4123 ≤ (7141553789319/50000000000000 : ℝ)^3099 := by
    have hnat : (2315972201 : ℕ)^4123*50000000000000^3099 ≤ 7141553789319^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315972201 10000000000 7141553789319 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611472491/5000000000 : ℝ)^4123 ≤ (1316911254271/3125000000000 : ℝ)^3099 := by
    have hnat : (2611472491 : ℕ)^4123*3125000000000^3099 ≤ 1316911254271^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611472491 5000000000 1316911254271 3125000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071205769/2000000000 : ℝ), (-2315972201/10000000000 : ℝ), (2611472491/5000000000 : ℝ)] ![(43575732269929/100000000000000 : ℝ), (7141553789319/50000000000000 : ℝ), (1316911254271/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071205769/2000000000 : ℝ)|^4123 ≤ (43575732269929/100000000000000 : ℝ)^3099
        have hw : |(1071205769/2000000000 : ℝ)|=(1071205769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2315972201/10000000000 : ℝ)|^4123 ≤ (7141553789319/50000000000000 : ℝ)^3099
        have hw : |(-2315972201/10000000000 : ℝ)|=(2315972201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611472491/5000000000 : ℝ)|^4123 ≤ (1316911254271/3125000000000 : ℝ)^3099
        have hw : |(2611472491/5000000000 : ℝ)|=(2611472491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339007189/2500000000 : ℝ)*x 0 + (5222944829/10000000000 : ℝ)*x 1 + (-1157986259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339007189/2500000000 : ℝ)^4123 ≤ (2178786565329/5000000000000 : ℝ)^3099 := by
    have hnat : (1339007189 : ℕ)^4123*5000000000000^3099 ≤ 2178786565329^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339007189 2500000000 2178786565329 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222944829/10000000000 : ℝ)^4123 ≤ (4214115849429/10000000000000 : ℝ)^3099 := by
    have hnat : (5222944829 : ℕ)^4123*10000000000000^3099 ≤ 4214115849429^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222944829 10000000000 4214115849429 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157986259/5000000000 : ℝ)^4123 ≤ (7141555089819/50000000000000 : ℝ)^3099 := by
    have hnat : (1157986259 : ℕ)^4123*50000000000000^3099 ≤ 7141555089819^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157986259 5000000000 7141555089819 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339007189/2500000000 : ℝ), (5222944829/10000000000 : ℝ), (-1157986259/5000000000 : ℝ)] ![(2178786565329/5000000000000 : ℝ), (4214115849429/10000000000000 : ℝ), (7141555089819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339007189/2500000000 : ℝ)|^4123 ≤ (2178786565329/5000000000000 : ℝ)^3099
        have hw : |(1339007189/2500000000 : ℝ)|=(1339007189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222944829/10000000000 : ℝ)|^4123 ≤ (4214115849429/10000000000000 : ℝ)^3099
        have hw : |(5222944829/10000000000 : ℝ)|=(5222944829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1157986259/5000000000 : ℝ)|^4123 ≤ (7141555089819/50000000000000 : ℝ)^3099
        have hw : |(-1157986259/5000000000 : ℝ)|=(1157986259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54680719/125000000 : ℝ)*x 0 + (416839359/1000000000 : ℝ)*x 1 + (2295435549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54680719/125000000 : ℝ)^4123 ≤ (33287032943933/100000000000000 : ℝ)^3099 := by
    have hnat : (54680719 : ℕ)^4123*100000000000000^3099 ≤ 33287032943933^3099*125000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54680719 125000000 33287032943933 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416839359/1000000000 : ℝ)^4123 ≤ (7804324289943/25000000000000 : ℝ)^3099 := by
    have hnat : (416839359 : ℕ)^4123*25000000000000^3099 ≤ 7804324289943^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416839359 1000000000 7804324289943 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2295435549/5000000000 : ℝ)^4123 ≤ (4436958736087/12500000000000 : ℝ)^3099 := by
    have hnat : (2295435549 : ℕ)^4123*12500000000000^3099 ≤ 4436958736087^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295435549 5000000000 4436958736087 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54680719/125000000 : ℝ), (416839359/1000000000 : ℝ), (2295435549/5000000000 : ℝ)] ![(33287032943933/100000000000000 : ℝ), (7804324289943/25000000000000 : ℝ), (4436958736087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54680719/125000000 : ℝ)|^4123 ≤ (33287032943933/100000000000000 : ℝ)^3099
        have hw : |(54680719/125000000 : ℝ)|=(54680719/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416839359/1000000000 : ℝ)|^4123 ≤ (7804324289943/25000000000000 : ℝ)^3099
        have hw : |(416839359/1000000000 : ℝ)|=(416839359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2295435549/5000000000 : ℝ)|^4123 ≤ (4436958736087/12500000000000 : ℝ)^3099
        have hw : |(2295435549/5000000000 : ℝ)|=(2295435549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220528699/1000000000 : ℝ)*x 0 + (652979847/1250000000 : ℝ)*x 1 + (5438168251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220528699/1000000000 : ℝ)^4123 ≤ (13382179098831/100000000000000 : ℝ)^3099 := by
    have hnat : (220528699 : ℕ)^4123*100000000000000^3099 ≤ 13382179098831^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220528699 1000000000 13382179098831 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652979847/1250000000 : ℝ)^4123 ≤ (843015097223/2000000000000 : ℝ)^3099 := by
    have hnat : (652979847 : ℕ)^4123*2000000000000^3099 ≤ 843015097223^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652979847 1250000000 843015097223 2000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438168251/10000000000 : ℝ)^4123 ≤ (2779191626737/6250000000000 : ℝ)^3099 := by
    have hnat : (5438168251 : ℕ)^4123*6250000000000^3099 ≤ 2779191626737^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438168251 10000000000 2779191626737 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220528699/1000000000 : ℝ), (652979847/1250000000 : ℝ), (5438168251/10000000000 : ℝ)] ![(13382179098831/100000000000000 : ℝ), (843015097223/2000000000000 : ℝ), (2779191626737/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220528699/1000000000 : ℝ)|^4123 ≤ (13382179098831/100000000000000 : ℝ)^3099
        have hw : |(-220528699/1000000000 : ℝ)|=(220528699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652979847/1250000000 : ℝ)|^4123 ≤ (843015097223/2000000000000 : ℝ)^3099
        have hw : |(652979847/1250000000 : ℝ)|=(652979847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438168251/10000000000 : ℝ)|^4123 ≤ (2779191626737/6250000000000 : ℝ)^3099
        have hw : |(5438168251/10000000000 : ℝ)|=(5438168251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301643513/10000000000 : ℝ)*x 0 + (-2100749541/10000000000 : ℝ)*x 1 + (5438167629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301643513/10000000000 : ℝ)^4123 ≤ (21494023716089/50000000000000 : ℝ)^3099 := by
    have hnat : (5301643513 : ℕ)^4123*50000000000000^3099 ≤ 21494023716089^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301643513 10000000000 21494023716089 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100749541/10000000000 : ℝ)^4123 ≤ (12544893298297/100000000000000 : ℝ)^3099 := by
    have hnat : (2100749541 : ℕ)^4123*100000000000000^3099 ≤ 12544893298297^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100749541 10000000000 12544893298297 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438167629/10000000000 : ℝ)^4123 ≤ (2779191203827/6250000000000 : ℝ)^3099 := by
    have hnat : (5438167629 : ℕ)^4123*6250000000000^3099 ≤ 2779191203827^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438167629 10000000000 2779191203827 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301643513/10000000000 : ℝ), (-2100749541/10000000000 : ℝ), (5438167629/10000000000 : ℝ)] ![(21494023716089/50000000000000 : ℝ), (12544893298297/100000000000000 : ℝ), (2779191203827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301643513/10000000000 : ℝ)|^4123 ≤ (21494023716089/50000000000000 : ℝ)^3099
        have hw : |(5301643513/10000000000 : ℝ)|=(5301643513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100749541/10000000000 : ℝ)|^4123 ≤ (12544893298297/100000000000000 : ℝ)^3099
        have hw : |(-2100749541/10000000000 : ℝ)|=(2100749541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438167629/10000000000 : ℝ)|^4123 ≤ (2779191203827/6250000000000 : ℝ)^3099
        have hw : |(5438167629/10000000000 : ℝ)|=(5438167629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650821599/5000000000 : ℝ)*x 0 + (2719084047/5000000000 : ℝ)*x 1 + (-210074933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650821599/5000000000 : ℝ)^4123 ≤ (42988044034051/100000000000000 : ℝ)^3099 := by
    have hnat : (2650821599 : ℕ)^4123*100000000000000^3099 ≤ 42988044034051^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650821599 5000000000 42988044034051 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719084047/5000000000 : ℝ)^4123 ≤ (22233532159917/50000000000000 : ℝ)^3099 := by
    have hnat : (2719084047 : ℕ)^4123*50000000000000^3099 ≤ 22233532159917^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719084047 5000000000 22233532159917 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210074933/1000000000 : ℝ)^4123 ≤ (6272445810969/50000000000000 : ℝ)^3099 := by
    have hnat : (210074933 : ℕ)^4123*50000000000000^3099 ≤ 6272445810969^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210074933 1000000000 6272445810969 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650821599/5000000000 : ℝ), (2719084047/5000000000 : ℝ), (-210074933/1000000000 : ℝ)] ![(42988044034051/100000000000000 : ℝ), (22233532159917/50000000000000 : ℝ), (6272445810969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650821599/5000000000 : ℝ)|^4123 ≤ (42988044034051/100000000000000 : ℝ)^3099
        have hw : |(2650821599/5000000000 : ℝ)|=(2650821599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719084047/5000000000 : ℝ)|^4123 ≤ (22233532159917/50000000000000 : ℝ)^3099
        have hw : |(2719084047/5000000000 : ℝ)|=(2719084047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210074933/1000000000 : ℝ)|^4123 ≤ (6272445810969/50000000000000 : ℝ)^3099
        have hw : |(-210074933/1000000000 : ℝ)|=(210074933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s3_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546812849/1250000000 : ℝ)*x 0 + (4589122727/10000000000 : ℝ)*x 1 + (834030479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546812849/1250000000 : ℝ)^4123 ≤ (33287491268423/100000000000000 : ℝ)^3099 := by
    have hnat : (546812849 : ℕ)^4123*100000000000000^3099 ≤ 33287491268423^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546812849 1250000000 33287491268423 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4589122727/10000000000 : ℝ)^4123 ≤ (35477686219639/100000000000000 : ℝ)^3099 := by
    have hnat : (4589122727 : ℕ)^4123*100000000000000^3099 ≤ 35477686219639^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589122727 10000000000 35477686219639 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834030479/2000000000 : ℝ)^4123 ≤ (7808705623409/25000000000000 : ℝ)^3099 := by
    have hnat : (834030479 : ℕ)^4123*25000000000000^3099 ≤ 7808705623409^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834030479 2000000000 7808705623409 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546812849/1250000000 : ℝ), (4589122727/10000000000 : ℝ), (834030479/2000000000 : ℝ)] ![(33287491268423/100000000000000 : ℝ), (35477686219639/100000000000000 : ℝ), (7808705623409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546812849/1250000000 : ℝ)|^4123 ≤ (33287491268423/100000000000000 : ℝ)^3099
        have hw : |(546812849/1250000000 : ℝ)|=(546812849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4589122727/10000000000 : ℝ)|^4123 ≤ (35477686219639/100000000000000 : ℝ)^3099
        have hw : |(4589122727/10000000000 : ℝ)|=(4589122727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834030479/2000000000 : ℝ)|^4123 ≤ (7808705623409/25000000000000 : ℝ)^3099
        have hw : |(834030479/2000000000 : ℝ)|=(834030479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (647/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (597/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1049/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1081/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1049/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1081/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1049/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1081/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1049/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1081/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1049/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1081/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1049/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1081/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1081/12500 : ℝ) ^ (8245/2048 : ℝ) ≤ (20507432891497/390625000000000000 : ℝ) := by
    have hpowers : (1081/12500 : ℝ)^8245 ≤ (20507432891497/390625000000000000 : ℝ)^2048 := by
      have hnat : (1081 : ℕ)^8245*390625000000000000^2048 ≤ 20507432891497^2048*12500^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1081 12500 20507432891497 390625000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1081/12500 : ℝ)) (X := (20507432891497/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1049/6250 : ℝ) ^ (8245/2048 : ℝ) ≤ (4735905667773451/6250000000000000000 : ℝ) := by
    have hpowers : (1049/6250 : ℝ)^8245 ≤ (4735905667773451/6250000000000000000 : ℝ)^2048 := by
      have hnat : (1049 : ℕ)^8245*6250000000000000000^2048 ≤ 4735905667773451^2048*6250^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1049 6250 4735905667773451 6250000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1049/6250 : ℝ)) (X := (4735905667773451/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (195333007432891497/195312500000000000 : ℝ) ≤ (5000130398747731/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (195333007432891497/195312500000000000 : ℝ)^2048 ≤ (5000130398747731/5000000000000000 : ℝ)^8245 := by
      have hnat : (195333007432891497 : ℕ)^2048*5000000000000000^8245 ≤ 5000130398747731^8245*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195333007432891497 195312500000000000 5000130398747731 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000130398747731/5000000000000000 : ℝ)) (X := (195333007432891497/195312500000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6255064024594037403/6250000000000000000 : ℝ) ≤ (10002011976408977/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (6255064024594037403/6250000000000000000 : ℝ)^2048 ≤ (10002011976408977/10000000000000000 : ℝ)^8245 := by
      have hnat : (6255064024594037403 : ℕ)^2048*10000000000000000^8245 ≤ 10002011976408977^8245*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255064024594037403 6250000000000000000 10002011976408977 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002011976408977/10000000000000000 : ℝ)) (X := (6255064024594037403/6250000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3129735905667773451/3125000000000000000 : ℝ) ≤ (2500940788830623/2500000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (3129735905667773451/3125000000000000000 : ℝ)^2048 ≤ (2500940788830623/2500000000000000 : ℝ)^8245 := by
      have hnat : (3129735905667773451 : ℕ)^2048*2500000000000000^8245 ≤ 2500940788830623^8245*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3129735905667773451 3125000000000000000 2500940788830623 2500000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500940788830623/2500000000000000 : ℝ)) (X := (3129735905667773451/3125000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20507432891497/390625000000000000 : ℝ) ≤ ((70600549876679621/70625000000000000 : ℝ)+2*(38915086967/18080000000000 : ℝ)*(1081/12500 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (70600549876679621/70625000000000000 : ℝ)+2*(38915086967/18080000000000 : ℝ)*(1081/12500 : ℝ)=(5000130398747731/5000000000000000 : ℝ) by norm_num, show 1+2*(20507432891497/390625000000000000 : ℝ)=(195333007432891497/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4735905667773451/6250000000000000000 : ℝ)+(20507432891497/390625000000000000 : ℝ) ≤ ((70600549876679621/70625000000000000 : ℝ)+(38915086967/18080000000000 : ℝ)*((1049/6250 : ℝ)+(1081/12500 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (70600549876679621/70625000000000000 : ℝ)+(38915086967/18080000000000 : ℝ)*((1049/6250 : ℝ)+(1081/12500 : ℝ))=(10002011976408977/10000000000000000 : ℝ) by norm_num, show 1+(4735905667773451/6250000000000000000 : ℝ)+(20507432891497/390625000000000000 : ℝ)=(6255064024594037403/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4735905667773451/6250000000000000000 : ℝ) ≤ ((70600549876679621/70625000000000000 : ℝ)+2*(38915086967/18080000000000 : ℝ)*(1049/6250 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (70600549876679621/70625000000000000 : ℝ)+2*(38915086967/18080000000000 : ℝ)*(1049/6250 : ℝ)=(2500940788830623/2500000000000000 : ℝ) by norm_num, show 1+2*(4735905667773451/6250000000000000000 : ℝ)=(3129735905667773451/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70600549876679621/70625000000000000 : ℝ)*(X 1 0+X 2 0)+(38915086967/18080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (1081/12500 : ℝ)) (hi := (1049/6250 : ℝ)) (c := (70600549876679621/70625000000000000 : ℝ)) (alpha := (38915086967/18080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70600549876679621/70625000000000000 : ℝ)*(X 0 1+X 2 1)+(38915086967/18080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (1081/12500 : ℝ)) (hi := (1049/6250 : ℝ)) (c := (70600549876679621/70625000000000000 : ℝ)) (alpha := (38915086967/18080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70600549876679621/70625000000000000 : ℝ)*(X 0 2+X 1 2)+(38915086967/18080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (1081/12500 : ℝ)) (hi := (1049/6250 : ℝ)) (c := (70600549876679621/70625000000000000 : ℝ)) (alpha := (38915086967/18080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205263893/10000000000 : ℝ)*X 0 0+(5439067221/10000000000 : ℝ)*X 0 1+(2611472551/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071205769/2000000000 : ℝ)*X 1 0+(-2315972201/10000000000 : ℝ)*X 1 1+(2611472491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339007189/2500000000 : ℝ)*X 2 0+(5222944829/10000000000 : ℝ)*X 2 1+(-1157986259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54680719/125000000 : ℝ)*X 0 0+(416839359/1000000000 : ℝ)*X 0 1+(2295435549/5000000000 : ℝ)*X 0 2+(54680719/125000000 : ℝ)*X 1 0+(416839359/1000000000 : ℝ)*X 1 1+(2295435549/5000000000 : ℝ)*X 1 2+(54680719/125000000 : ℝ)*X 2 0+(416839359/1000000000 : ℝ)*X 2 1+(2295435549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220528699/1000000000 : ℝ)*X 0 0+(652979847/1250000000 : ℝ)*X 0 1+(5438168251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301643513/10000000000 : ℝ)*X 1 0+(-2100749541/10000000000 : ℝ)*X 1 1+(5438167629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650821599/5000000000 : ℝ)*X 2 0+(2719084047/5000000000 : ℝ)*X 2 1+(-210074933/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546812849/1250000000 : ℝ)*X 0 0+(4589122727/10000000000 : ℝ)*X 0 1+(834030479/2000000000 : ℝ)*X 0 2+(546812849/1250000000 : ℝ)*X 1 0+(4589122727/10000000000 : ℝ)*X 1 1+(834030479/2000000000 : ℝ)*X 1 2+(546812849/1250000000 : ℝ)*X 2 0+(4589122727/10000000000 : ℝ)*X 2 1+(834030479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9043808679980104586439/904000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81109273/4000000000000 : ℝ)*(base19) + (964784987/50000000000000 : ℝ)*(base23) + (5697427/50000000000000 : ℝ)*(lower2) + (404239197/100000000000000 : ℝ)*(upper3) + (60419141/100000000000000 : ℝ)*(upper5) + (3497048589755339/100000000000000 : ℝ)*(major0) + (3497048589755339/100000000000000 : ℝ)*(major1) + (3497048589755339/100000000000000 : ℝ)*(major2) + (4627047586690873/100000000000000 : ℝ)*(sp0) + (4627069203934011/100000000000000 : ℝ)*(sp1) + (2313534651047931/50000000000000 : ℝ)*(sp2) + (2367005616683351/100000000000000 : ℝ)*(sp3) + (5911243741/25000000000000 : ℝ)*(sp4) + (1999768771/10000000000000 : ℝ)*(sp7) + (118351280718553/5000000000000 : ℝ)*(f.failure) + (1156767807916459/25000000000000 : ℝ)*(f.sum) + (5502144089349/904000000000000000000000000 : ℝ)*base65 + (94454090719810799/28250000000000000000000000000000 : ℝ)*base68 + (130255134948060799/28250000000000000000000000000000 : ℝ)*base70 + (198958887726689201/28250000000000000000000000000000 : ℝ)*base71 + (2496364885483/904000000000000000000000000 : ℝ)*base74 + (44755402322060799/28250000000000000000000000000000 : ℝ)*base76 + (268226182076439201/28250000000000000000000000000000 : ℝ)*base77 + (86102405551939201/28250000000000000000000000000000 : ℝ)*base79 + (388163653863/180800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4602423/500000000000000000000 : ℝ)*base90 + (4602423/500000000000000000000 : ℝ)*base92 + (4602423/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5453093929828160966372673/706250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190954647/12500000000000 : ℝ)*(base19) + (314487089/25000000000000 : ℝ)*(base23) + (4630347/20000000000000 : ℝ)*(lower4) + (171464971/50000000000000 : ℝ)*(upper5) + (176313052310937/5000000000000 : ℝ)*(major0) + (176313052310937/5000000000000 : ℝ)*(major1) + (176313052310937/5000000000000 : ℝ)*(major2) + (715162771/100000000000000 : ℝ)*(sp0) + (9805344441/50000000000000 : ℝ)*(sp1) + (16087450191/100000000000000 : ℝ)*(sp2) + (1166430662774569/25000000000000 : ℝ)*(sp4) + (466570222793499/10000000000000 : ℝ)*(sp5) + (373256481669/8000000000 : ℝ)*(sp6) + (2386798468803263/100000000000000 : ℝ)*(sp7) + (2386798468803263/100000000000000 : ℝ)*(f.failure) + (4665723366261047/100000000000000 : ℝ)*(f.sum) + (1107329612583/226000000000000000000000000 : ℝ)*base66 + (5079433121556117/1412500000000000000000000000000 : ℝ)*base68 + (3954320420993617/1412500000000000000000000000000 : ℝ)*base70 + (12167349205856117/1412500000000000000000000000000 : ℝ)*base72 + (840445257959/226000000000000000000000000 : ℝ)*base74 + (11282788402343617/1412500000000000000000000000000 : ℝ)*base76 + (2986023264206117/1412500000000000000000000000000 : ℝ)*base78 + (3171815900493883/1412500000000000000000000000000 : ℝ)*base79 + (40199988373/226000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (55501967/10000000000000000000000 : ℝ)*base89 + (55501967/10000000000000000000000 : ℝ)*base91 + (55501967/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1053_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (647/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (597/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s4_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209073201/10000000000 : ℝ)*x 0 + (5406546773/10000000000 : ℝ)*x 1 + (5252977327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209073201/10000000000 : ℝ)^4123 ≤ (3353188787887/25000000000000 : ℝ)^3099 := by
    have hnat : (2209073201 : ℕ)^4123*25000000000000^3099 ≤ 3353188787887^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209073201 10000000000 3353188787887 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406546773/10000000000 : ℝ)^4123 ≤ (22061697944651/50000000000000 : ℝ)^3099 := by
    have hnat : (5406546773 : ℕ)^4123*50000000000000^3099 ≤ 22061697944651^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406546773 10000000000 22061697944651 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252977327/10000000000 : ℝ)^4123 ≤ (42463848938243/100000000000000 : ℝ)^3099 := by
    have hnat : (5252977327 : ℕ)^4123*100000000000000^3099 ≤ 42463848938243^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252977327 10000000000 42463848938243 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209073201/10000000000 : ℝ), (5406546773/10000000000 : ℝ), (5252977327/10000000000 : ℝ)] ![(3353188787887/25000000000000 : ℝ), (22061697944651/50000000000000 : ℝ), (42463848938243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209073201/10000000000 : ℝ)|^4123 ≤ (3353188787887/25000000000000 : ℝ)^3099
        have hw : |(-2209073201/10000000000 : ℝ)|=(2209073201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406546773/10000000000 : ℝ)|^4123 ≤ (22061697944651/50000000000000 : ℝ)^3099
        have hw : |(5406546773/10000000000 : ℝ)|=(5406546773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252977327/10000000000 : ℝ)|^4123 ≤ (42463848938243/100000000000000 : ℝ)^3099
        have hw : |(5252977327/10000000000 : ℝ)|=(5252977327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347983819/10000000000 : ℝ)*x 0 + (-571798857/2500000000 : ℝ)*x 1 + (262648861/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347983819/10000000000 : ℝ)^4123 ≤ (21744336685221/50000000000000 : ℝ)^3099 := by
    have hnat : (5347983819 : ℕ)^4123*50000000000000^3099 ≤ 21744336685221^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347983819 10000000000 21744336685221 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571798857/2500000000 : ℝ)^4123 ≤ (14047478835591/100000000000000 : ℝ)^3099 := by
    have hnat : (571798857 : ℕ)^4123*100000000000000^3099 ≤ 14047478835591^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571798857 2500000000 14047478835591 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262648861/500000000 : ℝ)^4123 ≤ (42463847787471/100000000000000 : ℝ)^3099 := by
    have hnat : (262648861 : ℕ)^4123*100000000000000^3099 ≤ 42463847787471^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262648861 500000000 42463847787471 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347983819/10000000000 : ℝ), (-571798857/2500000000 : ℝ), (262648861/500000000 : ℝ)] ![(21744336685221/50000000000000 : ℝ), (14047478835591/100000000000000 : ℝ), (42463847787471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347983819/10000000000 : ℝ)|^4123 ≤ (21744336685221/50000000000000 : ℝ)^3099
        have hw : |(5347983819/10000000000 : ℝ)|=(5347983819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571798857/2500000000 : ℝ)|^4123 ≤ (14047478835591/100000000000000 : ℝ)^3099
        have hw : |(-571798857/2500000000 : ℝ)|=(571798857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262648861/500000000 : ℝ)|^4123 ≤ (42463847787471/100000000000000 : ℝ)^3099
        have hw : |(262648861/500000000 : ℝ)|=(262648861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213919353/400000000 : ℝ)*x 0 + (131324431/250000000 : ℝ)*x 1 + (-2287195393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213919353/400000000 : ℝ)^4123 ≤ (8697734687071/20000000000000 : ℝ)^3099 := by
    have hnat : (213919353 : ℕ)^4123*20000000000000^3099 ≤ 8697734687071^3099*400000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213919353 400000000 8697734687071 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131324431/250000000 : ℝ)^4123 ≤ (5307981000321/12500000000000 : ℝ)^3099 := by
    have hnat : (131324431 : ℕ)^4123*12500000000000^3099 ≤ 5307981000321^3099*250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131324431 250000000 5307981000321 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287195393/10000000000 : ℝ)^4123 ≤ (14047478549599/100000000000000 : ℝ)^3099 := by
    have hnat : (2287195393 : ℕ)^4123*100000000000000^3099 ≤ 14047478549599^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287195393 10000000000 14047478549599 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213919353/400000000 : ℝ), (131324431/250000000 : ℝ), (-2287195393/10000000000 : ℝ)] ![(8697734687071/20000000000000 : ℝ), (5307981000321/12500000000000 : ℝ), (14047478549599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213919353/400000000 : ℝ)|^4123 ≤ (8697734687071/20000000000000 : ℝ)^3099
        have hw : |(213919353/400000000 : ℝ)|=(213919353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131324431/250000000 : ℝ)|^4123 ≤ (5307981000321/12500000000000 : ℝ)^3099
        have hw : |(131324431/250000000 : ℝ)|=(131324431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2287195393/10000000000 : ℝ)|^4123 ≤ (14047478549599/100000000000000 : ℝ)^3099
        have hw : |(-2287195393/10000000000 : ℝ)|=(2287195393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875344083/2000000000 : ℝ)*x 0 + (4229235683/10000000000 : ℝ)*x 1 + (2264717017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875344083/2000000000 : ℝ)^4123 ≤ (2081871496857/6250000000000 : ℝ)^3099 := by
    have hnat : (875344083 : ℕ)^4123*6250000000000^3099 ≤ 2081871496857^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875344083 2000000000 2081871496857 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229235683/10000000000 : ℝ)^4123 ≤ (31824963432437/100000000000000 : ℝ)^3099 := by
    have hnat : (4229235683 : ℕ)^4123*100000000000000^3099 ≤ 31824963432437^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229235683 10000000000 31824963432437 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264717017/5000000000 : ℝ)^4123 ≤ (8716273151047/25000000000000 : ℝ)^3099 := by
    have hnat : (2264717017 : ℕ)^4123*25000000000000^3099 ≤ 8716273151047^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264717017 5000000000 8716273151047 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875344083/2000000000 : ℝ), (4229235683/10000000000 : ℝ), (2264717017/5000000000 : ℝ)] ![(2081871496857/6250000000000 : ℝ), (31824963432437/100000000000000 : ℝ), (8716273151047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875344083/2000000000 : ℝ)|^4123 ≤ (2081871496857/6250000000000 : ℝ)^3099
        have hw : |(875344083/2000000000 : ℝ)|=(875344083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229235683/10000000000 : ℝ)|^4123 ≤ (31824963432437/100000000000000 : ℝ)^3099
        have hw : |(4229235683/10000000000 : ℝ)|=(4229235683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264717017/5000000000 : ℝ)|^4123 ≤ (8716273151047/25000000000000 : ℝ)^3099
        have hw : |(2264717017/5000000000 : ℝ)|=(2264717017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104540703/5000000000 : ℝ)*x 0 + (1313357471/2500000000 : ℝ)*x 1 + (1351523097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104540703/5000000000 : ℝ)^4123 ≤ (6706410715469/50000000000000 : ℝ)^3099 := by
    have hnat : (1104540703 : ℕ)^4123*50000000000000^3099 ≤ 6706410715469^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104540703 5000000000 6706410715469 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313357471/2500000000 : ℝ)^4123 ≤ (21234358101983/50000000000000 : ℝ)^3099 := by
    have hnat : (1313357471 : ℕ)^4123*50000000000000^3099 ≤ 21234358101983^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313357471 2500000000 21234358101983 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351523097/2500000000 : ℝ)^4123 ≤ (44118462349007/100000000000000 : ℝ)^3099 := by
    have hnat : (1351523097 : ℕ)^4123*100000000000000^3099 ≤ 44118462349007^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351523097 2500000000 44118462349007 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104540703/5000000000 : ℝ), (1313357471/2500000000 : ℝ), (1351523097/2500000000 : ℝ)] ![(6706410715469/50000000000000 : ℝ), (21234358101983/50000000000000 : ℝ), (44118462349007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104540703/5000000000 : ℝ)|^4123 ≤ (6706410715469/50000000000000 : ℝ)^3099
        have hw : |(-1104540703/5000000000 : ℝ)|=(1104540703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313357471/2500000000 : ℝ)|^4123 ≤ (21234358101983/50000000000000 : ℝ)^3099
        have hw : |(1313357471/2500000000 : ℝ)|=(1313357471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351523097/2500000000 : ℝ)|^4123 ≤ (44118462349007/100000000000000 : ℝ)^3099
        have hw : |(1351523097/2500000000 : ℝ)|=(1351523097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327336227/2500000000 : ℝ)*x 0 + (-106703981/500000000 : ℝ)*x 1 + (1081218537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327336227/2500000000 : ℝ)^4123 ≤ (43071147721921/100000000000000 : ℝ)^3099 := by
    have hnat : (1327336227 : ℕ)^4123*100000000000000^3099 ≤ 43071147721921^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327336227 2500000000 43071147721921 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106703981/500000000 : ℝ)^4123 ≤ (51241546751/400000000000 : ℝ)^3099 := by
    have hnat : (106703981 : ℕ)^4123*400000000000^3099 ≤ 51241546751^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106703981 500000000 51241546751 400000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081218537/2000000000 : ℝ)^4123 ≤ (11029616393419/25000000000000 : ℝ)^3099 := by
    have hnat : (1081218537 : ℕ)^4123*25000000000000^3099 ≤ 11029616393419^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081218537 2000000000 11029616393419 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327336227/2500000000 : ℝ), (-106703981/500000000 : ℝ), (1081218537/2000000000 : ℝ)] ![(43071147721921/100000000000000 : ℝ), (51241546751/400000000000 : ℝ), (11029616393419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327336227/2500000000 : ℝ)|^4123 ≤ (43071147721921/100000000000000 : ℝ)^3099
        have hw : |(1327336227/2500000000 : ℝ)|=(1327336227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106703981/500000000 : ℝ)|^4123 ≤ (51241546751/400000000000 : ℝ)^3099
        have hw : |(-106703981/500000000 : ℝ)|=(106703981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081218537/2000000000 : ℝ)|^4123 ≤ (11029616393419/25000000000000 : ℝ)^3099
        have hw : |(1081218537/2000000000 : ℝ)|=(1081218537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82958511/156250000 : ℝ)*x 0 + (5406092561/10000000000 : ℝ)*x 1 + (-426816013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82958511/156250000 : ℝ)^4123 ≤ (21535572760087/50000000000000 : ℝ)^3099 := by
    have hnat : (82958511 : ℕ)^4123*50000000000000^3099 ≤ 21535572760087^3099*156250000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82958511 156250000 21535572760087 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406092561/10000000000 : ℝ)^4123 ≤ (44118464227349/100000000000000 : ℝ)^3099 := by
    have hnat : (5406092561 : ℕ)^4123*100000000000000^3099 ≤ 44118464227349^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406092561 10000000000 44118464227349 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426816013/2000000000 : ℝ)^4123 ≤ (2562078048327/20000000000000 : ℝ)^3099 := by
    have hnat : (426816013 : ℕ)^4123*20000000000000^3099 ≤ 2562078048327^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426816013 2000000000 2562078048327 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82958511/156250000 : ℝ), (5406092561/10000000000 : ℝ), (-426816013/2000000000 : ℝ)] ![(21535572760087/50000000000000 : ℝ), (44118464227349/100000000000000 : ℝ), (2562078048327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82958511/156250000 : ℝ)|^4123 ≤ (21535572760087/50000000000000 : ℝ)^3099
        have hw : |(82958511/156250000 : ℝ)|=(82958511/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406092561/10000000000 : ℝ)|^4123 ≤ (44118464227349/100000000000000 : ℝ)^3099
        have hw : |(5406092561/10000000000 : ℝ)|=(5406092561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426816013/2000000000 : ℝ)|^4123 ≤ (2562078048327/20000000000000 : ℝ)^3099
        have hw : |(-426816013/2000000000 : ℝ)|=(426816013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s4_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273546033/625000000 : ℝ)*x 0 + (2264274513/5000000000 : ℝ)*x 1 + (4230124617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273546033/625000000 : ℝ)^4123 ≤ (6662021420427/20000000000000 : ℝ)^3099 := by
    have hnat : (273546033 : ℕ)^4123*20000000000000^3099 ≤ 6662021420427^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273546033 625000000 6662021420427 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264274513/5000000000 : ℝ)^4123 ≤ (8714007401889/25000000000000 : ℝ)^3099 := by
    have hnat : (2264274513 : ℕ)^4123*25000000000000^3099 ≤ 8714007401889^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264274513 5000000000 8714007401889 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230124617/10000000000 : ℝ)^4123 ≤ (3979232909523/12500000000000 : ℝ)^3099 := by
    have hnat : (4230124617 : ℕ)^4123*12500000000000^3099 ≤ 3979232909523^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230124617 10000000000 3979232909523 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273546033/625000000 : ℝ), (2264274513/5000000000 : ℝ), (4230124617/10000000000 : ℝ)] ![(6662021420427/20000000000000 : ℝ), (8714007401889/25000000000000 : ℝ), (3979232909523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273546033/625000000 : ℝ)|^4123 ≤ (6662021420427/20000000000000 : ℝ)^3099
        have hw : |(273546033/625000000 : ℝ)|=(273546033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264274513/5000000000 : ℝ)|^4123 ≤ (8714007401889/25000000000000 : ℝ)^3099
        have hw : |(2264274513/5000000000 : ℝ)|=(2264274513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230124617/10000000000 : ℝ)|^4123 ≤ (3979232909523/12500000000000 : ℝ)^3099
        have hw : |(4230124617/10000000000 : ℝ)|=(4230124617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (597/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (647/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5497/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (597/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (647/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (597/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (647/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (597/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (647/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (597/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (647/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (597/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (647/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (597/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (647/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (647/6250 : ℝ) ^ (8245/2048 : ℝ) ≤ (2165892783170413/20000000000000000000 : ℝ) := by
    have hpowers : (647/6250 : ℝ)^8245 ≤ (2165892783170413/20000000000000000000 : ℝ)^2048 := by
      have hnat : (647 : ℕ)^8245*20000000000000000000^2048 ≤ 2165892783170413^2048*6250^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        647 6250 2165892783170413 20000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (647/6250 : ℝ)) (X := (2165892783170413/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (597/4000 : ℝ) ^ (8245/2048 : ℝ) ≤ (47236658241066391/100000000000000000000 : ℝ) := by
    have hpowers : (597/4000 : ℝ)^8245 ≤ (47236658241066391/100000000000000000000 : ℝ)^2048 := by
      have hnat : (597 : ℕ)^8245*100000000000000000000^2048 ≤ 47236658241066391^2048*4000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        597 4000 47236658241066391 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (597/4000 : ℝ)) (X := (47236658241066391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002165892783170413/10000000000000000000 : ℝ) ≤ (10000537948746851/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (10002165892783170413/10000000000000000000 : ℝ)^2048 ≤ (10000537948746851/10000000000000000 : ℝ)^8245 := by
      have hnat : (10002165892783170413 : ℕ)^2048*10000000000000000^8245 ≤ 10000537948746851^8245*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002165892783170413 10000000000000000000 10000537948746851 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537948746851/10000000000000000 : ℝ)) (X := (10002165892783170413/10000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507258265269614807/12500000000000000000 : ℝ) ≤ (5000721003499253/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (12507258265269614807/12500000000000000000 : ℝ)^2048 ≤ (5000721003499253/5000000000000000 : ℝ)^8245 := by
      have hnat : (12507258265269614807 : ℕ)^2048*5000000000000000^8245 ≤ 5000721003499253^8245*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507258265269614807 12500000000000000000 5000721003499253 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000721003499253/5000000000000000 : ℝ)) (X := (12507258265269614807/12500000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047236658241066391/50000000000000000000 : ℝ) ≤ (10002346065250161/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50047236658241066391/50000000000000000000 : ℝ)^2048 ≤ (10002346065250161/10000000000000000 : ℝ)^8245 := by
      have hnat : (50047236658241066391 : ℕ)^2048*10000000000000000^8245 ≤ 10002346065250161^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047236658241066391 50000000000000000000 10002346065250161 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002346065250161/10000000000000000 : ℝ)) (X := (50047236658241066391/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2165892783170413/20000000000000000000 : ℝ) ≤ ((45713742417577084503/45730000000000000000 : ℝ)+2*(180811650331/91460000000000 : ℝ)*(647/6250 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (45713742417577084503/45730000000000000000 : ℝ)+2*(180811650331/91460000000000 : ℝ)*(647/6250 : ℝ)=(10000537948746851/10000000000000000 : ℝ) by norm_num, show 1+2*(2165892783170413/20000000000000000000 : ℝ)=(10002165892783170413/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47236658241066391/100000000000000000000 : ℝ)+(2165892783170413/20000000000000000000 : ℝ) ≤ ((45713742417577084503/45730000000000000000 : ℝ)+(180811650331/91460000000000 : ℝ)*((597/4000 : ℝ)+(647/6250 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (45713742417577084503/45730000000000000000 : ℝ)+(180811650331/91460000000000 : ℝ)*((597/4000 : ℝ)+(647/6250 : ℝ))=(5000721003499253/5000000000000000 : ℝ) by norm_num, show 1+(47236658241066391/100000000000000000000 : ℝ)+(2165892783170413/20000000000000000000 : ℝ)=(12507258265269614807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47236658241066391/100000000000000000000 : ℝ) ≤ ((45713742417577084503/45730000000000000000 : ℝ)+2*(180811650331/91460000000000 : ℝ)*(597/4000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (45713742417577084503/45730000000000000000 : ℝ)+2*(180811650331/91460000000000 : ℝ)*(597/4000 : ℝ)=(10002346065250161/10000000000000000 : ℝ) by norm_num, show 1+2*(47236658241066391/100000000000000000000 : ℝ)=(50047236658241066391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45713742417577084503/45730000000000000000 : ℝ)*(X 1 0+X 2 0)+(180811650331/91460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (647/6250 : ℝ)) (hi := (597/4000 : ℝ)) (c := (45713742417577084503/45730000000000000000 : ℝ)) (alpha := (180811650331/91460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45713742417577084503/45730000000000000000 : ℝ)*(X 0 1+X 2 1)+(180811650331/91460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (647/6250 : ℝ)) (hi := (597/4000 : ℝ)) (c := (45713742417577084503/45730000000000000000 : ℝ)) (alpha := (180811650331/91460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45713742417577084503/45730000000000000000 : ℝ)*(X 0 2+X 1 2)+(180811650331/91460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (647/6250 : ℝ)) (hi := (597/4000 : ℝ)) (c := (45713742417577084503/45730000000000000000 : ℝ)) (alpha := (180811650331/91460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209073201/10000000000 : ℝ)*X 0 0+(5406546773/10000000000 : ℝ)*X 0 1+(5252977327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347983819/10000000000 : ℝ)*X 1 0+(-571798857/2500000000 : ℝ)*X 1 1+(262648861/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213919353/400000000 : ℝ)*X 2 0+(131324431/250000000 : ℝ)*X 2 1+(-2287195393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875344083/2000000000 : ℝ)*X 0 0+(4229235683/10000000000 : ℝ)*X 0 1+(2264717017/5000000000 : ℝ)*X 0 2+(875344083/2000000000 : ℝ)*X 1 0+(4229235683/10000000000 : ℝ)*X 1 1+(2264717017/5000000000 : ℝ)*X 1 2+(875344083/2000000000 : ℝ)*X 2 0+(4229235683/10000000000 : ℝ)*X 2 1+(2264717017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104540703/5000000000 : ℝ)*X 0 0+(1313357471/2500000000 : ℝ)*X 0 1+(1351523097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327336227/2500000000 : ℝ)*X 1 0+(-106703981/500000000 : ℝ)*X 1 1+(1081218537/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82958511/156250000 : ℝ)*X 2 0+(5406092561/10000000000 : ℝ)*X 2 1+(-426816013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273546033/625000000 : ℝ)*X 0 0+(2264274513/5000000000 : ℝ)*X 0 1+(4230124617/10000000000 : ℝ)*X 0 2+(273546033/625000000 : ℝ)*X 1 0+(2264274513/5000000000 : ℝ)*X 1 1+(4230124617/10000000000 : ℝ)*X 1 2+(273546033/625000000 : ℝ)*X 2 0+(2264274513/5000000000 : ℝ)*X 2 1+(4230124617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5096767030030315281556655883/1143250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (532844149/50000000000000 : ℝ)*(base19) + (208543043/20000000000000 : ℝ)*(base23) + (16193019/100000000000000 : ℝ)*(lower2) + (90874141/100000000000000 : ℝ)*(upper3) + (115947529/100000000000000 : ℝ)*(upper5) + (4921455269883487/100000000000000 : ℝ)*(major0) + (4921455269883487/100000000000000 : ℝ)*(major1) + (4921455269883487/100000000000000 : ℝ)*(major2) + (6511732897622699/100000000000000 : ℝ)*(sp0) + (6511754385870913/100000000000000 : ℝ)*(sp1) + (1627938602210999/25000000000000 : ℝ)*(sp2) + (3331143004828113/100000000000000 : ℝ)*(sp3) + (22553936511/100000000000000 : ℝ)*(sp4) + (1491846877/12500000000000 : ℝ)*(sp7) + (333115493960313/10000000000000 : ℝ)*(f.failure) + (651175545155921/10000000000000 : ℝ)*(f.sum) + (7141274355397/4573000000000000000000000000 : ℝ)*base66 + (9937795154903801961/4573000000000000000000000000000000 : ℝ)*base67 + (32263243193953198039/4573000000000000000000000000000000 : ℝ)*base70 + (19554773461508198039/4573000000000000000000000000000000 : ℝ)*base72 + (845352003983/2286500000000000000000000000 : ℝ)*base74 + (143157020774840198039/4573000000000000000000000000000000 : ℝ)*base76 + (77218510630577198039/4573000000000000000000000000000000 : ℝ)*base78 + (55559253382793198039/4573000000000000000000000000000000 : ℝ)*base80 + (8515539388319/4573000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10325417/1000000000000000000000 : ℝ)*base89 + (10325417/1000000000000000000000 : ℝ)*base91 + (10325417/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5951048053043559370413/571625000000000000000000000 : ℝ) := by norm_num
    linear_combination (124619883/5000000000000 : ℝ)*(base19) + (2211407109/100000000000000 : ℝ)*(base23) + (22630677/100000000000000 : ℝ)*(upper3) + (21166713/25000000000000 : ℝ)*(lower4) + (142858599/50000000000000 : ℝ)*(upper5) + (4950663665781547/100000000000000 : ℝ)*(major0) + (4950663665781547/100000000000000 : ℝ)*(major1) + (4950663665781547/100000000000000 : ℝ)*(major2) + (1720140607/2000000000000 : ℝ)*(sp1) + (30033748377/50000000000000 : ℝ)*(sp2) + (6550401938952281/100000000000000 : ℝ)*(sp4) + (6550313439524271/100000000000000 : ℝ)*(sp5) + (3275169830024209/50000000000000 : ℝ)*(sp6) + (418865630698203/12500000000000 : ℝ)*(sp7) + (418865630698203/12500000000000 : ℝ)*(f.failure) + (6550401938952281/100000000000000 : ℝ)*(f.sum) + (30904319198879/4573000000000000000000000000 : ℝ)*base65 + (2693330859341566141/4573000000000000000000000000000000 : ℝ)*base67 + (20403865081442433859/4573000000000000000000000000000000 : ℝ)*base70 + (13975038187315566141/4573000000000000000000000000000000 : ℝ)*base71 + (145441754087/914600000000000000000000000 : ℝ)*base74 + (32853160688253433859/4573000000000000000000000000000000 : ℝ)*base76 + (35896790123776433859/4573000000000000000000000000000000 : ℝ)*base78 + (60632636976399566141/4573000000000000000000000000000000 : ℝ)*base79 + (30676683810389/4573000000000000000000000000 : ℝ)*base81 + (10355573/1250000000000000000000 : ℝ)*base90 + (10355573/1250000000000000000000 : ℝ)*base92 + (10355573/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1053_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (597/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (647/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s5_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-552484297/2500000000 : ℝ)*x 0 + (1079475693/2000000000 : ℝ)*x 1 + (105231589/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552484297/2500000000 : ℝ)^4123 ≤ (13419734821963/100000000000000 : ℝ)^3099 := by
    have hnat : (552484297 : ℕ)^4123*100000000000000^3099 ≤ 13419734821963^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552484297 2500000000 13419734821963 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079475693/2000000000 : ℝ)^4123 ≤ (88047752781/200000000000 : ℝ)^3099 := by
    have hnat : (1079475693 : ℕ)^4123*200000000000^3099 ≤ 88047752781^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079475693 2000000000 88047752781 200000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105231589/200000000 : ℝ)^4123 ≤ (10639097190949/25000000000000 : ℝ)^3099 := by
    have hnat : (105231589 : ℕ)^4123*25000000000000^3099 ≤ 10639097190949^3099*200000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105231589 200000000 10639097190949 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552484297/2500000000 : ℝ), (1079475693/2000000000 : ℝ), (105231589/200000000 : ℝ)] ![(13419734821963/100000000000000 : ℝ), (88047752781/200000000000 : ℝ), (10639097190949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552484297/2500000000 : ℝ)|^4123 ≤ (13419734821963/100000000000000 : ℝ)^3099
        have hw : |(-552484297/2500000000 : ℝ)|=(552484297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079475693/2000000000 : ℝ)|^4123 ≤ (88047752781/200000000000 : ℝ)^3099
        have hw : |(1079475693/2000000000 : ℝ)|=(1079475693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105231589/200000000 : ℝ)|^4123 ≤ (10639097190949/25000000000000 : ℝ)^3099
        have hw : |(105231589/200000000 : ℝ)|=(105231589/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336426167/2500000000 : ℝ)*x 0 + (-1139441413/5000000000 : ℝ)*x 1 + (65769741/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336426167/2500000000 : ℝ)^4123 ≤ (8692803499873/20000000000000 : ℝ)^3099 := by
    have hnat : (1336426167 : ℕ)^4123*20000000000000^3099 ≤ 8692803499873^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336426167 2500000000 8692803499873 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139441413/5000000000 : ℝ)^4123 ≤ (6989797779821/50000000000000 : ℝ)^3099 := by
    have hnat : (1139441413 : ℕ)^4123*50000000000000^3099 ≤ 6989797779821^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139441413 5000000000 6989797779821 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65769741/125000000 : ℝ)^4123 ≤ (42556386934477/100000000000000 : ℝ)^3099 := by
    have hnat : (65769741 : ℕ)^4123*100000000000000^3099 ≤ 42556386934477^3099*125000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65769741 125000000 42556386934477 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336426167/2500000000 : ℝ), (-1139441413/5000000000 : ℝ), (65769741/125000000 : ℝ)] ![(8692803499873/20000000000000 : ℝ), (6989797779821/50000000000000 : ℝ), (42556386934477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336426167/2500000000 : ℝ)|^4123 ≤ (8692803499873/20000000000000 : ℝ)^3099
        have hw : |(1336426167/2500000000 : ℝ)|=(1336426167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139441413/5000000000 : ℝ)|^4123 ≤ (6989797779821/50000000000000 : ℝ)^3099
        have hw : |(-1139441413/5000000000 : ℝ)|=(1139441413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65769741/125000000 : ℝ)|^4123 ≤ (42556386934477/100000000000000 : ℝ)^3099
        have hw : |(65769741/125000000 : ℝ)|=(65769741/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069140891/2000000000 : ℝ)*x 0 + (5261579447/10000000000 : ℝ)*x 1 + (-2278882887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069140891/2000000000 : ℝ)^4123 ≤ (10866003798823/25000000000000 : ℝ)^3099 := by
    have hnat : (1069140891 : ℕ)^4123*25000000000000^3099 ≤ 10866003798823^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069140891 2000000000 10866003798823 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261579447/10000000000 : ℝ)^4123 ≤ (42556388731513/100000000000000 : ℝ)^3099 := by
    have hnat : (5261579447 : ℕ)^4123*100000000000000^3099 ≤ 42556388731513^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261579447 10000000000 42556388731513 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278882887/10000000000 : ℝ)^4123 ≤ (13979596057487/100000000000000 : ℝ)^3099 := by
    have hnat : (2278882887 : ℕ)^4123*100000000000000^3099 ≤ 13979596057487^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278882887 10000000000 13979596057487 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069140891/2000000000 : ℝ), (5261579447/10000000000 : ℝ), (-2278882887/10000000000 : ℝ)] ![(10866003798823/25000000000000 : ℝ), (42556388731513/100000000000000 : ℝ), (13979596057487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069140891/2000000000 : ℝ)|^4123 ≤ (10866003798823/25000000000000 : ℝ)^3099
        have hw : |(1069140891/2000000000 : ℝ)|=(1069140891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261579447/10000000000 : ℝ)|^4123 ≤ (42556388731513/100000000000000 : ℝ)^3099
        have hw : |(5261579447/10000000000 : ℝ)|=(5261579447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278882887/10000000000 : ℝ)|^4123 ≤ (13979596057487/100000000000000 : ℝ)^3099
        have hw : |(-2278882887/10000000000 : ℝ)|=(2278882887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377223657/10000000000 : ℝ)*x 0 + (2123269069/5000000000 : ℝ)*x 1 + (2255999567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377223657/10000000000 : ℝ)^4123 ≤ (33315039627811/100000000000000 : ℝ)^3099 := by
    have hnat : (4377223657 : ℕ)^4123*100000000000000^3099 ≤ 33315039627811^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377223657 10000000000 33315039627811 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123269069/5000000000 : ℝ)^4123 ≤ (31998303393043/100000000000000 : ℝ)^3099 := by
    have hnat : (2123269069 : ℕ)^4123*100000000000000^3099 ≤ 31998303393043^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123269069 5000000000 31998303393043 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255999567/5000000000 : ℝ)^4123 ≤ (3468665697051/10000000000000 : ℝ)^3099 := by
    have hnat : (2255999567 : ℕ)^4123*10000000000000^3099 ≤ 3468665697051^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255999567 5000000000 3468665697051 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377223657/10000000000 : ℝ), (2123269069/5000000000 : ℝ), (2255999567/5000000000 : ℝ)] ![(33315039627811/100000000000000 : ℝ), (31998303393043/100000000000000 : ℝ), (3468665697051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377223657/10000000000 : ℝ)|^4123 ≤ (33315039627811/100000000000000 : ℝ)^3099
        have hw : |(4377223657/10000000000 : ℝ)|=(4377223657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123269069/5000000000 : ℝ)|^4123 ≤ (31998303393043/100000000000000 : ℝ)^3099
        have hw : |(2123269069/5000000000 : ℝ)|=(2123269069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255999567/5000000000 : ℝ)|^4123 ≤ (3468665697051/10000000000000 : ℝ)^3099
        have hw : |(2255999567/5000000000 : ℝ)|=(2255999567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220994319/1000000000 : ℝ)*x 0 + (526193339/1000000000 : ℝ)*x 1 + (5397023017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220994319/1000000000 : ℝ)^4123 ≤ (13419783311937/100000000000000 : ℝ)^3099 := by
    have hnat : (220994319 : ℕ)^4123*100000000000000^3099 ≤ 13419783311937^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220994319 1000000000 13419783311937 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526193339/1000000000 : ℝ)^4123 ≤ (42560197447139/100000000000000 : ℝ)^3099 := by
    have hnat : (526193339 : ℕ)^4123*100000000000000^3099 ≤ 42560197447139^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526193339 1000000000 42560197447139 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397023017/10000000000 : ℝ)^4123 ≤ (22010009611421/50000000000000 : ℝ)^3099 := by
    have hnat : (5397023017 : ℕ)^4123*50000000000000^3099 ≤ 22010009611421^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397023017 10000000000 22010009611421 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220994319/1000000000 : ℝ), (526193339/1000000000 : ℝ), (5397023017/10000000000 : ℝ)] ![(13419783311937/100000000000000 : ℝ), (42560197447139/100000000000000 : ℝ), (22010009611421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220994319/1000000000 : ℝ)|^4123 ≤ (13419783311937/100000000000000 : ℝ)^3099
        have hw : |(-220994319/1000000000 : ℝ)|=(220994319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526193339/1000000000 : ℝ)|^4123 ≤ (42560197447139/100000000000000 : ℝ)^3099
        have hw : |(526193339/1000000000 : ℝ)|=(526193339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397023017/10000000000 : ℝ)|^4123 ≤ (22010009611421/50000000000000 : ℝ)^3099
        have hw : |(5397023017/10000000000 : ℝ)|=(5397023017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655767731/5000000000 : ℝ)*x 0 + (-267929899/1250000000 : ℝ)*x 1 + (1349255761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655767731/5000000000 : ℝ)^4123 ≤ (43094791715221/100000000000000 : ℝ)^3099 := by
    have hnat : (2655767731 : ℕ)^4123*100000000000000^3099 ≤ 43094791715221^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655767731 5000000000 43094791715221 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267929899/1250000000 : ℝ)^4123 ≤ (12885188760849/100000000000000 : ℝ)^3099 := by
    have hnat : (267929899 : ℕ)^4123*100000000000000^3099 ≤ 12885188760849^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267929899 1250000000 12885188760849 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349255761/2500000000 : ℝ)^4123 ≤ (44020019515831/100000000000000 : ℝ)^3099 := by
    have hnat : (1349255761 : ℕ)^4123*100000000000000^3099 ≤ 44020019515831^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349255761 2500000000 44020019515831 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655767731/5000000000 : ℝ), (-267929899/1250000000 : ℝ), (1349255761/2500000000 : ℝ)] ![(43094791715221/100000000000000 : ℝ), (12885188760849/100000000000000 : ℝ), (44020019515831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655767731/5000000000 : ℝ)|^4123 ≤ (43094791715221/100000000000000 : ℝ)^3099
        have hw : |(2655767731/5000000000 : ℝ)|=(2655767731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267929899/1250000000 : ℝ)|^4123 ≤ (12885188760849/100000000000000 : ℝ)^3099
        have hw : |(-267929899/1250000000 : ℝ)|=(267929899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349255761/2500000000 : ℝ)|^4123 ≤ (44020019515831/100000000000000 : ℝ)^3099
        have hw : |(1349255761/2500000000 : ℝ)|=(1349255761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327883847/2500000000 : ℝ)*x 0 + (2698511543/5000000000 : ℝ)*x 1 + (-428687847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327883847/2500000000 : ℝ)^4123 ≤ (43094790916439/100000000000000 : ℝ)^3099 := by
    have hnat : (1327883847 : ℕ)^4123*100000000000000^3099 ≤ 43094790916439^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327883847 2500000000 43094790916439 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698511543/5000000000 : ℝ)^4123 ≤ (5502502496449/12500000000000 : ℝ)^3099 := by
    have hnat : (2698511543 : ℕ)^4123*12500000000000^3099 ≤ 5502502496449^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698511543 5000000000 5502502496449 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428687847/2000000000 : ℝ)^4123 ≤ (2577037820951/20000000000000 : ℝ)^3099 := by
    have hnat : (428687847 : ℕ)^4123*20000000000000^3099 ≤ 2577037820951^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428687847 2000000000 2577037820951 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327883847/2500000000 : ℝ), (2698511543/5000000000 : ℝ), (-428687847/2000000000 : ℝ)] ![(43094790916439/100000000000000 : ℝ), (5502502496449/12500000000000 : ℝ), (2577037820951/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327883847/2500000000 : ℝ)|^4123 ≤ (43094790916439/100000000000000 : ℝ)^3099
        have hw : |(1327883847/2500000000 : ℝ)|=(1327883847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698511543/5000000000 : ℝ)|^4123 ≤ (5502502496449/12500000000000 : ℝ)^3099
        have hw : |(2698511543/5000000000 : ℝ)|=(2698511543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428687847/2000000000 : ℝ)|^4123 ≤ (2577037820951/20000000000000 : ℝ)^3099
        have hw : |(-428687847/2000000000 : ℝ)|=(428687847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s5_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547154383/1250000000 : ℝ)*x 0 + (2255653401/5000000000 : ℝ)*x 1 + (2123616461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547154383/1250000000 : ℝ)^4123 ≤ (4164394391741/12500000000000 : ℝ)^3099 := by
    have hnat : (547154383 : ℕ)^4123*12500000000000^3099 ≤ 4164394391741^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547154383 1250000000 4164394391741 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255653401/5000000000 : ℝ)^4123 ≤ (34679576068383/100000000000000 : ℝ)^3099 := by
    have hnat : (2255653401 : ℕ)^4123*100000000000000^3099 ≤ 34679576068383^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255653401 5000000000 34679576068383 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123616461/5000000000 : ℝ)^4123 ≤ (32005268779691/100000000000000 : ℝ)^3099 := by
    have hnat : (2123616461 : ℕ)^4123*100000000000000^3099 ≤ 32005268779691^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123616461 5000000000 32005268779691 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547154383/1250000000 : ℝ), (2255653401/5000000000 : ℝ), (2123616461/5000000000 : ℝ)] ![(4164394391741/12500000000000 : ℝ), (34679576068383/100000000000000 : ℝ), (32005268779691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547154383/1250000000 : ℝ)|^4123 ≤ (4164394391741/12500000000000 : ℝ)^3099
        have hw : |(547154383/1250000000 : ℝ)|=(547154383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255653401/5000000000 : ℝ)|^4123 ≤ (34679576068383/100000000000000 : ℝ)^3099
        have hw : |(2255653401/5000000000 : ℝ)|=(2255653401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123616461/5000000000 : ℝ)|^4123 ≤ (32005268779691/100000000000000 : ℝ)^3099
        have hw : |(2123616461/5000000000 : ℝ)|=(2123616461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11177/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5497/50000 : ℝ) ^ (8245/2048 : ℝ) ≤ (13797775984157791/100000000000000000000 : ℝ) := by
    have hpowers : (5497/50000 : ℝ)^8245 ≤ (13797775984157791/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5497 : ℕ)^8245*100000000000000000000^2048 ≤ 13797775984157791^2048*50000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 50000 13797775984157791 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/50000 : ℝ)) (X := (13797775984157791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7123/50000 : ℝ) ^ (8245/2048 : ℝ) ≤ (3916248657116177/10000000000000000000 : ℝ) := by
    have hpowers : (7123/50000 : ℝ)^8245 ≤ (3916248657116177/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7123 : ℕ)^8245*10000000000000000000^2048 ≤ 3916248657116177^2048*50000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7123 50000 3916248657116177 10000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7123/50000 : ℝ)) (X := (3916248657116177/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013797775984157791/50000000000000000000 : ℝ) ≤ (2000137076605003/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50013797775984157791/50000000000000000000 : ℝ)^2048 ≤ (2000137076605003/2000000000000000 : ℝ)^8245 := by
      have hnat : (50013797775984157791 : ℕ)^2048*2000000000000000^8245 ≤ 2000137076605003^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013797775984157791 50000000000000000000 2000137076605003 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000137076605003/2000000000000000 : ℝ)) (X := (50013797775984157791/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052960262555319561/100000000000000000000 : ℝ) ≤ (10001315233929019/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (100052960262555319561/100000000000000000000 : ℝ)^2048 ≤ (10001315233929019/10000000000000000 : ℝ)^8245 := by
      have hnat : (100052960262555319561 : ℕ)^2048*10000000000000000^8245 ≤ 10001315233929019^8245*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052960262555319561 100000000000000000000 10001315233929019 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001315233929019/10000000000000000 : ℝ)) (X := (100052960262555319561/100000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003916248657116177/5000000000000000000 : ℝ) ≤ (10001945084833023/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (5003916248657116177/5000000000000000000 : ℝ)^2048 ≤ (10001945084833023/10000000000000000 : ℝ)^8245 := by
      have hnat : (5003916248657116177 : ℕ)^2048*10000000000000000^8245 ≤ 10001945084833023^8245*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003916248657116177 5000000000000000000 10001945084833023 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001945084833023/10000000000000000 : ℝ)) (X := (5003916248657116177/5000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13797775984157791/100000000000000000000 : ℝ) ≤ ((8127094925980027207/8130000000000000000 : ℝ)+2*(157462726001/81300000000000 : ℝ)*(5497/50000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (8127094925980027207/8130000000000000000 : ℝ)+2*(157462726001/81300000000000 : ℝ)*(5497/50000 : ℝ)=(2000137076605003/2000000000000000 : ℝ) by norm_num, show 1+2*(13797775984157791/100000000000000000000 : ℝ)=(50013797775984157791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3916248657116177/10000000000000000000 : ℝ)+(13797775984157791/100000000000000000000 : ℝ) ≤ ((8127094925980027207/8130000000000000000 : ℝ)+(157462726001/81300000000000 : ℝ)*((7123/50000 : ℝ)+(5497/50000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (8127094925980027207/8130000000000000000 : ℝ)+(157462726001/81300000000000 : ℝ)*((7123/50000 : ℝ)+(5497/50000 : ℝ))=(10001315233929019/10000000000000000 : ℝ) by norm_num, show 1+(3916248657116177/10000000000000000000 : ℝ)+(13797775984157791/100000000000000000000 : ℝ)=(100052960262555319561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3916248657116177/10000000000000000000 : ℝ) ≤ ((8127094925980027207/8130000000000000000 : ℝ)+2*(157462726001/81300000000000 : ℝ)*(7123/50000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (8127094925980027207/8130000000000000000 : ℝ)+2*(157462726001/81300000000000 : ℝ)*(7123/50000 : ℝ)=(10001945084833023/10000000000000000 : ℝ) by norm_num, show 1+2*(3916248657116177/10000000000000000000 : ℝ)=(5003916248657116177/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8127094925980027207/8130000000000000000 : ℝ)*(X 1 0+X 2 0)+(157462726001/81300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8127094925980027207/8130000000000000000 : ℝ)) (alpha := (157462726001/81300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8127094925980027207/8130000000000000000 : ℝ)*(X 0 1+X 2 1)+(157462726001/81300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8127094925980027207/8130000000000000000 : ℝ)) (alpha := (157462726001/81300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8127094925980027207/8130000000000000000 : ℝ)*(X 0 2+X 1 2)+(157462726001/81300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (8127094925980027207/8130000000000000000 : ℝ)) (alpha := (157462726001/81300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552484297/2500000000 : ℝ)*X 0 0+(1079475693/2000000000 : ℝ)*X 0 1+(105231589/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336426167/2500000000 : ℝ)*X 1 0+(-1139441413/5000000000 : ℝ)*X 1 1+(65769741/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069140891/2000000000 : ℝ)*X 2 0+(5261579447/10000000000 : ℝ)*X 2 1+(-2278882887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377223657/10000000000 : ℝ)*X 0 0+(2123269069/5000000000 : ℝ)*X 0 1+(2255999567/5000000000 : ℝ)*X 0 2+(4377223657/10000000000 : ℝ)*X 1 0+(2123269069/5000000000 : ℝ)*X 1 1+(2255999567/5000000000 : ℝ)*X 1 2+(4377223657/10000000000 : ℝ)*X 2 0+(2123269069/5000000000 : ℝ)*X 2 1+(2255999567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220994319/1000000000 : ℝ)*X 0 0+(526193339/1000000000 : ℝ)*X 0 1+(5397023017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655767731/5000000000 : ℝ)*X 1 0+(-267929899/1250000000 : ℝ)*X 1 1+(1349255761/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327883847/2500000000 : ℝ)*X 2 0+(2698511543/5000000000 : ℝ)*X 2 1+(-428687847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547154383/1250000000 : ℝ)*X 0 0+(2255653401/5000000000 : ℝ)*X 0 1+(2123616461/5000000000 : ℝ)*X 0 2+(547154383/1250000000 : ℝ)*X 1 0+(2255653401/5000000000 : ℝ)*X 1 1+(2123616461/5000000000 : ℝ)*X 1 2+(547154383/1250000000 : ℝ)*X 2 0+(2255653401/5000000000 : ℝ)*X 2 1+(2123616461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18539398858338124347048203/2117187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (71562877/4000000000000 : ℝ)*(base19) + (57028201/4000000000000 : ℝ)*(base23) + (47607561/50000000000000 : ℝ)*(lower2) + (40305303/20000000000000 : ℝ)*(upper3) + (14455299/25000000000000 : ℝ)*(lower4) + (43480453472501/781250000000 : ℝ)*(major0) + (43480453472501/781250000000 : ℝ)*(major1) + (43480453472501/781250000000 : ℝ)*(major2) + (7363873146523721/100000000000000 : ℝ)*(sp0) + (3681954912734079/50000000000000 : ℝ)*(sp1) + (3681955094417529/50000000000000 : ℝ)*(sp2) + (3767056503322869/100000000000000 : ℝ)*(sp3) + (19234008181/50000000000000 : ℝ)*(sp4) + (5535842017/20000000000000 : ℝ)*(sp7) + (1883542091266477/50000000000000 : ℝ)*(f.failure) + (7363911614540083/100000000000000 : ℝ)*(f.sum) + (1615960860203/4065000000000000000000000000 : ℝ)*base65 + (57592088035638763/4234375000000000000000000000000 : ℝ)*base67 + (1785416515719681/2117187500000000000000000000000 : ℝ)*base70 + (985080167173737/4234375000000000000000000000000 : ℝ)*base72 + (280020114427/254062500000000000000000000 : ℝ)*base74 + (8210717768500931/2117187500000000000000000000000 : ℝ)*base76 + (14978935171329987/4234375000000000000000000000000 : ℝ)*base78 + (2999603683867653/1058593750000000000000000000000 : ℝ)*base80 + (10710482280461/2032500000000000000000000000 : ℝ)*base82 + (13326307/5000000000000000000000 : ℝ)*base90 + (13326307/5000000000000000000000 : ℝ)*base92 + (13326307/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118281651658561996180876113/67750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338186837/50000000000000 : ℝ)*(base19) + (609254251/100000000000000 : ℝ)*(base23) + (2150269/10000000000000 : ℝ)*(upper2) + (46937753/50000000000000 : ℝ)*(upper3) + (7323821/12500000000000 : ℝ)*(upper5) + (2797327148668759/50000000000000 : ℝ)*(major0) + (2797327148668759/50000000000000 : ℝ)*(major1) + (2797327148668759/50000000000000 : ℝ)*(major2) + (17530852047/100000000000000 : ℝ)*(sp1) + (16835852901/100000000000000 : ℝ)*(sp2) + (7402489541701327/100000000000000 : ℝ)*(sp4) + (7402471334475607/100000000000000 : ℝ)*(sp5) + (296098883863767/4000000000000 : ℝ)*(sp6) + (1893409497389271/50000000000000 : ℝ)*(sp7) + (1893409497389271/50000000000000 : ℝ)*(f.failure) + (7402489541701327/100000000000000 : ℝ)*(f.sum) + (5128780530281/508125000000000000000000000 : ℝ)*base65 + (876207951854724629/135500000000000000000000000000000 : ℝ)*base68 + (704387457204224629/135500000000000000000000000000000 : ℝ)*base70 + (825444908953275371/135500000000000000000000000000000 : ℝ)*base71 + (328227474553/254062500000000000000000000 : ℝ)*base73 + (2156572164073724629/135500000000000000000000000000000 : ℝ)*base76 + (829806921565775371/135500000000000000000000000000000 : ℝ)*base77 + (1027485743533224629/135500000000000000000000000000000 : ℝ)*base80 + (15156812180369/2032500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (48102361/5000000000000000000000 : ℝ)*base90 + (48102361/5000000000000000000000 : ℝ)*base92 + (48102361/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1053_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1053_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1053_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1053_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1053_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
