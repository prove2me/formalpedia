-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:57.039269+00:00
-- url     : https://prove2.me/submissions/498cf70d-5c25-4d71-83be-295bd512411e

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
theorem support_rectangle_w1175_s0_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-37628201/200000000 : ℝ)*x 0 + (604673439/1000000000 : ℝ)*x 1 + (1196157931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37628201/200000000 : ℝ)^523 ≤ (10949123779271/100000000000000 : ℝ)^395 := by
    have hnat : (37628201 : ℕ)^523*100000000000000^395 ≤ 10949123779271^395*200000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37628201 200000000 10949123779271 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604673439/1000000000 : ℝ)^523 ≤ (12842885410277/25000000000000 : ℝ)^395 := by
    have hnat : (604673439 : ℕ)^523*25000000000000^395 ≤ 12842885410277^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604673439 1000000000 12842885410277 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196157931/2500000000 : ℝ)^523 ≤ (37679334562057/100000000000000 : ℝ)^395 := by
    have hnat : (1196157931 : ℕ)^523*100000000000000^395 ≤ 37679334562057^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196157931 2500000000 37679334562057 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37628201/200000000 : ℝ), (604673439/1000000000 : ℝ), (1196157931/2500000000 : ℝ)] ![(10949123779271/100000000000000 : ℝ), (12842885410277/25000000000000 : ℝ), (37679334562057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37628201/200000000 : ℝ)|^523 ≤ (10949123779271/100000000000000 : ℝ)^395
        have hw : |(-37628201/200000000 : ℝ)|=(37628201/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604673439/1000000000 : ℝ)|^523 ≤ (12842885410277/25000000000000 : ℝ)^395
        have hw : |(604673439/1000000000 : ℝ)|=(604673439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196157931/2500000000 : ℝ)|^523 ≤ (37679334562057/100000000000000 : ℝ)^395
        have hw : |(1196157931/2500000000 : ℝ)|=(1196157931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (110298689/200000000 : ℝ)*x 0 + (-520956067/2000000000 : ℝ)*x 1 + (4784631719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110298689/200000000 : ℝ)^523 ≤ (454764277949/1000000000000 : ℝ)^395 := by
    have hnat : (110298689 : ℕ)^523*1000000000000^395 ≤ 454764277949^395*200000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110298689 200000000 454764277949 1000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520956067/2000000000 : ℝ)^523 ≤ (16844237689073/100000000000000 : ℝ)^395 := by
    have hnat : (520956067 : ℕ)^523*100000000000000^395 ≤ 16844237689073^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520956067 2000000000 16844237689073 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4784631719/10000000000 : ℝ)^523 ≤ (18839667254961/50000000000000 : ℝ)^395 := by
    have hnat : (4784631719 : ℕ)^523*50000000000000^395 ≤ 18839667254961^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784631719 10000000000 18839667254961 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110298689/200000000 : ℝ), (-520956067/2000000000 : ℝ), (4784631719/10000000000 : ℝ)] ![(454764277949/1000000000000 : ℝ), (16844237689073/100000000000000 : ℝ), (18839667254961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110298689/200000000 : ℝ)|^523 ≤ (454764277949/1000000000000 : ℝ)^395
        have hw : |(110298689/200000000 : ℝ)|=(110298689/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520956067/2000000000 : ℝ)|^523 ≤ (16844237689073/100000000000000 : ℝ)^395
        have hw : |(-520956067/2000000000 : ℝ)|=(520956067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4784631719/10000000000 : ℝ)|^523 ≤ (18839667254961/50000000000000 : ℝ)^395
        have hw : |(4784631719/10000000000 : ℝ)|=(4784631719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1378733631/2500000000 : ℝ)*x 0 + (4784631649/10000000000 : ℝ)*x 1 + (-104191213/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378733631/2500000000 : ℝ)^523 ≤ (22738214301423/50000000000000 : ℝ)^395 := by
    have hnat : (1378733631 : ℕ)^523*50000000000000^395 ≤ 22738214301423^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378733631 2500000000 22738214301423 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784631649/10000000000 : ℝ)^523 ≤ (588739590313/1562500000000 : ℝ)^395 := by
    have hnat : (4784631649 : ℕ)^523*1562500000000^395 ≤ 588739590313^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784631649 10000000000 588739590313 1562500000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104191213/400000000 : ℝ)^523 ≤ (4211059400863/25000000000000 : ℝ)^395 := by
    have hnat : (104191213 : ℕ)^523*25000000000000^395 ≤ 4211059400863^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104191213 400000000 4211059400863 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378733631/2500000000 : ℝ), (4784631649/10000000000 : ℝ), (-104191213/400000000 : ℝ)] ![(22738214301423/50000000000000 : ℝ), (588739590313/1562500000000 : ℝ), (4211059400863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378733631/2500000000 : ℝ)|^523 ≤ (22738214301423/50000000000000 : ℝ)^395
        have hw : |(1378733631/2500000000 : ℝ)|=(1378733631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784631649/10000000000 : ℝ)|^523 ≤ (588739590313/1562500000000 : ℝ)^395
        have hw : |(4784631649/10000000000 : ℝ)|=(4784631649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104191213/400000000 : ℝ)|^523 ≤ (4211059400863/25000000000000 : ℝ)^395
        have hw : |(-104191213/400000000 : ℝ)|=(104191213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2099167479/5000000000 : ℝ)*x 0 + (779899709/2500000000 : ℝ)*x 1 + (176461953/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099167479/5000000000 : ℝ)^523 ≤ (990341544063/3125000000000 : ℝ)^395 := by
    have hnat : (2099167479 : ℕ)^523*3125000000000^395 ≤ 990341544063^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099167479 5000000000 990341544063 3125000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779899709/2500000000 : ℝ)^523 ≤ (10693777250577/50000000000000 : ℝ)^395 := by
    have hnat : (779899709 : ℕ)^523*50000000000000^395 ≤ 10693777250577^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779899709 2500000000 10693777250577 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176461953/312500000 : ℝ)^523 ≤ (46921516080411/100000000000000 : ℝ)^395 := by
    have hnat : (176461953 : ℕ)^523*100000000000000^395 ≤ 46921516080411^395*312500000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176461953 312500000 46921516080411 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099167479/5000000000 : ℝ), (779899709/2500000000 : ℝ), (176461953/312500000 : ℝ)] ![(990341544063/3125000000000 : ℝ), (10693777250577/50000000000000 : ℝ), (46921516080411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099167479/5000000000 : ℝ)|^523 ≤ (990341544063/3125000000000 : ℝ)^395
        have hw : |(2099167479/5000000000 : ℝ)|=(2099167479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779899709/2500000000 : ℝ)|^523 ≤ (10693777250577/50000000000000 : ℝ)^395
        have hw : |(779899709/2500000000 : ℝ)|=(779899709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176461953/312500000 : ℝ)|^523 ≤ (46921516080411/100000000000000 : ℝ)^395
        have hw : |(176461953/312500000 : ℝ)|=(176461953/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1886459321/10000000000 : ℝ)*x 0 + (4817173071/10000000000 : ℝ)*x 1 + (3006523249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1886459321/10000000000 : ℝ)^523 ≤ (10988047815891/100000000000000 : ℝ)^395 := by
    have hnat : (1886459321 : ℕ)^523*100000000000000^395 ≤ 10988047815891^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886459321 10000000000 10988047815891 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817173071/10000000000 : ℝ)^523 ≤ (19009508233991/50000000000000 : ℝ)^395 := by
    have hnat : (4817173071 : ℕ)^523*50000000000000^395 ≤ 19009508233991^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817173071 10000000000 19009508233991 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3006523249/5000000000 : ℝ)^523 ≤ (50992935691283/100000000000000 : ℝ)^395 := by
    have hnat : (3006523249 : ℕ)^523*100000000000000^395 ≤ 50992935691283^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006523249 5000000000 50992935691283 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1886459321/10000000000 : ℝ), (4817173071/10000000000 : ℝ), (3006523249/5000000000 : ℝ)] ![(10988047815891/100000000000000 : ℝ), (19009508233991/50000000000000 : ℝ), (50992935691283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1886459321/10000000000 : ℝ)|^523 ≤ (10988047815891/100000000000000 : ℝ)^395
        have hw : |(-1886459321/10000000000 : ℝ)|=(1886459321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817173071/10000000000 : ℝ)|^523 ≤ (19009508233991/50000000000000 : ℝ)^395
        have hw : |(4817173071/10000000000 : ℝ)|=(4817173071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3006523249/5000000000 : ℝ)|^523 ≤ (50992935691283/100000000000000 : ℝ)^395
        have hw : |(3006523249/5000000000 : ℝ)|=(3006523249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2585917629/5000000000 : ℝ)*x 0 + (-1376365749/10000000000 : ℝ)*x 1 + (1202609249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585917629/5000000000 : ℝ)^523 ≤ (835374196401/2000000000000 : ℝ)^395 := by
    have hnat : (2585917629 : ℕ)^523*2000000000000^395 ≤ 835374196401^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585917629 5000000000 835374196401 2000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376365749/10000000000 : ℝ)^523 ≤ (3619178656639/50000000000000 : ℝ)^395 := by
    have hnat : (1376365749 : ℕ)^523*50000000000000^395 ≤ 3619178656639^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376365749 10000000000 3619178656639 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202609249/2000000000 : ℝ)^523 ≤ (50992932850483/100000000000000 : ℝ)^395 := by
    have hnat : (1202609249 : ℕ)^523*100000000000000^395 ≤ 50992932850483^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202609249 2000000000 50992932850483 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585917629/5000000000 : ℝ), (-1376365749/10000000000 : ℝ), (1202609249/2000000000 : ℝ)] ![(835374196401/2000000000000 : ℝ), (3619178656639/50000000000000 : ℝ), (50992932850483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585917629/5000000000 : ℝ)|^523 ≤ (835374196401/2000000000000 : ℝ)^395
        have hw : |(2585917629/5000000000 : ℝ)|=(2585917629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376365749/10000000000 : ℝ)|^523 ≤ (3619178656639/50000000000000 : ℝ)^395
        have hw : |(-1376365749/10000000000 : ℝ)|=(1376365749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1202609249/2000000000 : ℝ)|^523 ≤ (50992932850483/100000000000000 : ℝ)^395
        have hw : |(1202609249/2000000000 : ℝ)|=(1202609249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2585917607/5000000000 : ℝ)*x 0 + (3006523183/5000000000 : ℝ)*x 1 + (-688182811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585917607/5000000000 : ℝ)^523 ≤ (20884354674773/50000000000000 : ℝ)^395 := by
    have hnat : (2585917607 : ℕ)^523*50000000000000^395 ≤ 20884354674773^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585917607 5000000000 20884354674773 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3006523183/5000000000 : ℝ)^523 ≤ (50992934209127/100000000000000 : ℝ)^395 := by
    have hnat : (3006523183 : ℕ)^523*100000000000000^395 ≤ 50992934209127^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006523183 5000000000 50992934209127 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688182811/5000000000 : ℝ)^523 ≤ (1809589107237/25000000000000 : ℝ)^395 := by
    have hnat : (688182811 : ℕ)^523*25000000000000^395 ≤ 1809589107237^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688182811 5000000000 1809589107237 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585917607/5000000000 : ℝ), (3006523183/5000000000 : ℝ), (-688182811/5000000000 : ℝ)] ![(20884354674773/50000000000000 : ℝ), (50992934209127/100000000000000 : ℝ), (1809589107237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585917607/5000000000 : ℝ)|^523 ≤ (20884354674773/50000000000000 : ℝ)^395
        have hw : |(2585917607/5000000000 : ℝ)|=(2585917607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3006523183/5000000000 : ℝ)|^523 ≤ (50992934209127/100000000000000 : ℝ)^395
        have hw : |(3006523183/5000000000 : ℝ)|=(3006523183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688182811/5000000000 : ℝ)|^523 ≤ (1809589107237/25000000000000 : ℝ)^395
        have hw : |(-688182811/5000000000 : ℝ)|=(688182811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s0_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4208445427/10000000000 : ℝ)*x 0 + (21803213/39062500 : ℝ)*x 1 + (637410879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208445427/10000000000 : ℝ)^523 ≤ (31792018228113/100000000000000 : ℝ)^395 := by
    have hnat : (4208445427 : ℕ)^523*100000000000000^395 ≤ 31792018228113^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208445427 10000000000 31792018228113 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21803213/39062500 : ℝ)^523 ≤ (46205963481519/100000000000000 : ℝ)^395 := by
    have hnat : (21803213 : ℕ)^523*100000000000000^395 ≤ 46205963481519^395*39062500^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21803213 39062500 46205963481519 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637410879/2000000000 : ℝ)^523 ≤ (11001009140499/50000000000000 : ℝ)^395 := by
    have hnat : (637410879 : ℕ)^523*50000000000000^395 ≤ 11001009140499^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637410879 2000000000 11001009140499 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208445427/10000000000 : ℝ), (21803213/39062500 : ℝ), (637410879/2000000000 : ℝ)] ![(31792018228113/100000000000000 : ℝ), (46205963481519/100000000000000 : ℝ), (11001009140499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208445427/10000000000 : ℝ)|^523 ≤ (31792018228113/100000000000000 : ℝ)^395
        have hw : |(4208445427/10000000000 : ℝ)|=(4208445427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21803213/39062500 : ℝ)|^523 ≤ (46205963481519/100000000000000 : ℝ)^395
        have hw : |(21803213/39062500 : ℝ)|=(21803213/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637410879/2000000000 : ℝ)|^523 ≤ (11001009140499/50000000000000 : ℝ)^395
        have hw : |(637410879/2000000000 : ℝ)|=(637410879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (549/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27689/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8367/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8367 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8367*1^2048 ≤ 0^2048*1^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8367/2048 : ℝ) ≤ (118360368005613823/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8367 ≤ (118360368005613823/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8367*5000000000000000000^2048 ≤ 118360368005613823^2048*5^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 118360368005613823 5000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (118360368005613823/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8367 := by
      have hnat : (1 : ℕ)^2048*1^8367 ≤ 1^8367*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5118360368005613823/5000000000000000000 : ℝ) ≤ (5028715758522117/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (5118360368005613823/5000000000000000000 : ℝ)^2048 ≤ (5028715758522117/5000000000000000 : ℝ)^8367 := by
      have hnat : (5118360368005613823 : ℕ)^2048*5000000000000000^8367 ≤ 5028715758522117^8367*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5118360368005613823 5000000000000000000 5028715758522117 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028715758522117/5000000000000000 : ℝ)) (X := (5118360368005613823/5000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2618360368005613823/2500000000000000000 : ℝ) ≤ (2528715758522117/2500000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (2618360368005613823/2500000000000000000 : ℝ)^2048 ≤ (2528715758522117/2500000000000000 : ℝ)^8367 := by
      have hnat : (2618360368005613823 : ℕ)^2048*2500000000000000^8367 ≤ 2528715758522117^8367*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2618360368005613823 2500000000000000000 2528715758522117 2500000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528715758522117/2500000000000000 : ℝ)) (X := (2618360368005613823/2500000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28715758522117/2000000000000000 : ℝ)*(0 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28715758522117/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(118360368005613823/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28715758522117/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28715758522117/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028715758522117/5000000000000000 : ℝ) by norm_num, show 1+(118360368005613823/5000000000000000000 : ℝ)+(0 : ℝ)=(5118360368005613823/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(118360368005613823/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28715758522117/2000000000000000 : ℝ)*(2/5 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28715758522117/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528715758522117/2500000000000000 : ℝ) by norm_num, show 1+2*(118360368005613823/5000000000000000000 : ℝ)=(2618360368005613823/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28715758522117/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28715758522117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28715758522117/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28715758522117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28715758522117/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28715758522117/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37628201/200000000 : ℝ)*X 0 0+(604673439/1000000000 : ℝ)*X 0 1+(1196157931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((110298689/200000000 : ℝ)*X 1 0+(-520956067/2000000000 : ℝ)*X 1 1+(4784631719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378733631/2500000000 : ℝ)*X 2 0+(4784631649/10000000000 : ℝ)*X 2 1+(-104191213/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099167479/5000000000 : ℝ)*X 0 0+(779899709/2500000000 : ℝ)*X 0 1+(176461953/312500000 : ℝ)*X 0 2+(2099167479/5000000000 : ℝ)*X 1 0+(779899709/2500000000 : ℝ)*X 1 1+(176461953/312500000 : ℝ)*X 1 2+(2099167479/5000000000 : ℝ)*X 2 0+(779899709/2500000000 : ℝ)*X 2 1+(176461953/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1886459321/10000000000 : ℝ)*X 0 0+(4817173071/10000000000 : ℝ)*X 0 1+(3006523249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585917629/5000000000 : ℝ)*X 1 0+(-1376365749/10000000000 : ℝ)*X 1 1+(1202609249/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585917607/5000000000 : ℝ)*X 2 0+(3006523183/5000000000 : ℝ)*X 2 1+(-688182811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208445427/10000000000 : ℝ)*X 0 0+(21803213/39062500 : ℝ)*X 0 1+(637410879/2000000000 : ℝ)*X 0 2+(4208445427/10000000000 : ℝ)*X 1 0+(21803213/39062500 : ℝ)*X 1 1+(637410879/2000000000 : ℝ)*X 1 2+(4208445427/10000000000 : ℝ)*X 2 0+(21803213/39062500 : ℝ)*X 2 1+(637410879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (933292681738361067/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (542467/2000000000000 : ℝ)*(base1) + (432502667/100000000000000 : ℝ)*(base19) + (413534703/100000000000000 : ℝ)*(base23) + (29599543/100000000000000 : ℝ)*(base24) + (46365847/50000000000000 : ℝ)*(upper3) + (29700740828851/5000000000000 : ℝ)*(major0) + (29700740828851/5000000000000 : ℝ)*(major1) + (29700740828851/5000000000000 : ℝ)*(major2) + (79232999121727/10000000000000 : ℝ)*(sp0) + (396165252034837/50000000000000 : ℝ)*(sp1) + (49520655839881/6250000000000 : ℝ)*(sp2) + (98924462779631/25000000000000 : ℝ)*(sp3) + (48623921/5000000000000 : ℝ)*(sp4) + (151224061/20000000000000 : ℝ)*(sp7) + (197849317181089/50000000000000 : ℝ)*(f.failure) + (792330936572341/100000000000000 : ℝ)*(f.sum) + (9355309337433/5000000000000000000000000000 : ℝ)*base66 + (41851272957567/10000000000000000000000000000 : ℝ)*base67 + (9195465007567/10000000000000000000000000000 : ℝ)*base69 + (22491870072433/10000000000000000000000000000 : ℝ)*base72 + (2785353627567/5000000000000000000000000000 : ℝ)*base73 + (7065964652433/10000000000000000000000000000 : ℝ)*base76 + (29935440112433/10000000000000000000000000000 : ℝ)*base78 + (53352298882433/10000000000000000000000000000 : ℝ)*base80 + (4046969302567/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (7842867/1000000000000000000000 : ℝ)*base90 + (7842867/1000000000000000000000 : ℝ)*base92 + (7842867/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97764916045514332677201/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14770467/25000000000000 : ℝ)*(base1) + (1228769579/100000000000000 : ℝ)*(base19) + (244648269/20000000000000 : ℝ)*(base23) + (32187947/25000000000000 : ℝ)*(upper3) + (2971699/2000000000000 : ℝ)*(upper5) + (125382096911649/20000000000000 : ℝ)*(major0) + (125382096911649/20000000000000 : ℝ)*(major1) + (125382096911649/20000000000000 : ℝ)*(major2) + (495713239/20000000000000 : ℝ)*(sp1) + (2502471029/100000000000000 : ℝ)*(sp2) + (836209021773689/100000000000000 : ℝ)*(sp4) + (836205255356047/100000000000000 : ℝ)*(sp5) + (836205236979447/100000000000000 : ℝ)*(sp6) + (417611784401273/100000000000000 : ℝ)*(sp7) + (417611843483141/100000000000000 : ℝ)*(f.failure) + (836208962691821/100000000000000 : ℝ)*(f.sum) + (10106306599067/20000000000000000000000000000 : ℝ)*base66 + (2674121079067/40000000000000000000000000000 : ℝ)*base68 + (146428723160933/40000000000000000000000000000 : ℝ)*base69 + (12395896439067/40000000000000000000000000000 : ℝ)*base72 + (9436789120933/20000000000000000000000000000 : ℝ)*base73 + (50447059240933/40000000000000000000000000000 : ℝ)*base75 + (7534944440933/40000000000000000000000000000 : ℝ)*base77 + (56750421239067/40000000000000000000000000000 : ℝ)*base80 + (77054773920933/20000000000000000000000000000 : ℝ)*base81 + (1678177/2000000000000000000000 : ℝ)*base89 + (1678177/2000000000000000000000 : ℝ)*base91 + (1678177/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (549/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s1_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-416736993/2000000000 : ℝ)*x 0 + (2846387203/5000000000 : ℝ)*x 1 + (1252276537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416736993/2000000000 : ℝ)^523 ≤ (6267136583999/50000000000000 : ℝ)^395 := by
    have hnat : (416736993 : ℕ)^523*50000000000000^395 ≤ 6267136583999^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416736993 2000000000 6267136583999 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2846387203/5000000000 : ℝ)^523 ≤ (47428190190487/100000000000000 : ℝ)^395 := by
    have hnat : (2846387203 : ℕ)^523*100000000000000^395 ≤ 47428190190487^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846387203 5000000000 47428190190487 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252276537/2500000000 : ℝ)^523 ≤ (40037536632007/100000000000000 : ℝ)^395 := by
    have hnat : (1252276537 : ℕ)^523*100000000000000^395 ≤ 40037536632007^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252276537 2500000000 40037536632007 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416736993/2000000000 : ℝ), (2846387203/5000000000 : ℝ), (1252276537/2500000000 : ℝ)] ![(6267136583999/50000000000000 : ℝ), (47428190190487/100000000000000 : ℝ), (40037536632007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416736993/2000000000 : ℝ)|^523 ≤ (6267136583999/50000000000000 : ℝ)^395
        have hw : |(-416736993/2000000000 : ℝ)|=(416736993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2846387203/5000000000 : ℝ)|^523 ≤ (47428190190487/100000000000000 : ℝ)^395
        have hw : |(2846387203/5000000000 : ℝ)|=(2846387203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252276537/2500000000 : ℝ)|^523 ≤ (40037536632007/100000000000000 : ℝ)^395
        have hw : |(1252276537/2500000000 : ℝ)|=(1252276537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (677164041/1250000000 : ℝ)*x 0 + (-1226007709/5000000000 : ℝ)*x 1 + (1252276299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677164041/1250000000 : ℝ)^523 ≤ (4441364032339/10000000000000 : ℝ)^395 := by
    have hnat : (677164041 : ℕ)^523*10000000000000^395 ≤ 4441364032339^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677164041 1250000000 4441364032339 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226007709/5000000000 : ℝ)^523 ≤ (15548833108847/100000000000000 : ℝ)^395 := by
    have hnat : (1226007709 : ℕ)^523*100000000000000^395 ≤ 15548833108847^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226007709 5000000000 15548833108847 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252276299/2500000000 : ℝ)^523 ≤ (10009381639231/25000000000000 : ℝ)^395 := by
    have hnat : (1252276299 : ℕ)^523*25000000000000^395 ≤ 10009381639231^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252276299 2500000000 10009381639231 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677164041/1250000000 : ℝ), (-1226007709/5000000000 : ℝ), (1252276299/2500000000 : ℝ)] ![(4441364032339/10000000000000 : ℝ), (15548833108847/100000000000000 : ℝ), (10009381639231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677164041/1250000000 : ℝ)|^523 ≤ (4441364032339/10000000000000 : ℝ)^395
        have hw : |(677164041/1250000000 : ℝ)|=(677164041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1226007709/5000000000 : ℝ)|^523 ≤ (15548833108847/100000000000000 : ℝ)^395
        have hw : |(-1226007709/5000000000 : ℝ)|=(1226007709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252276299/2500000000 : ℝ)|^523 ≤ (10009381639231/25000000000000 : ℝ)^395
        have hw : |(1252276299/2500000000 : ℝ)|=(1252276299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5417314433/10000000000 : ℝ)*x 0 + (5009103213/10000000000 : ℝ)*x 1 + (-613003799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417314433/10000000000 : ℝ)^523 ≤ (11103415793387/25000000000000 : ℝ)^395 := by
    have hnat : (5417314433 : ℕ)^523*25000000000000^395 ≤ 11103415793387^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417314433 10000000000 11103415793387 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5009103213/10000000000 : ℝ)^523 ≤ (40037505570697/100000000000000 : ℝ)^395 := by
    have hnat : (5009103213 : ℕ)^523*100000000000000^395 ≤ 40037505570697^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009103213 10000000000 40037505570697 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613003799/2500000000 : ℝ)^523 ≤ (7774415622453/50000000000000 : ℝ)^395 := by
    have hnat : (613003799 : ℕ)^523*50000000000000^395 ≤ 7774415622453^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613003799 2500000000 7774415622453 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417314433/10000000000 : ℝ), (5009103213/10000000000 : ℝ), (-613003799/2500000000 : ℝ)] ![(11103415793387/25000000000000 : ℝ), (40037505570697/100000000000000 : ℝ), (7774415622453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417314433/10000000000 : ℝ)|^523 ≤ (11103415793387/25000000000000 : ℝ)^395
        have hw : |(5417314433/10000000000 : ℝ)|=(5417314433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5009103213/10000000000 : ℝ)|^523 ≤ (40037505570697/100000000000000 : ℝ)^395
        have hw : |(5009103213/10000000000 : ℝ)|=(5009103213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-613003799/2500000000 : ℝ)|^523 ≤ (7774415622453/50000000000000 : ℝ)^395
        have hw : |(-613003799/2500000000 : ℝ)|=(613003799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2157316817/5000000000 : ℝ)*x 0 + (3683207627/10000000000 : ℝ)*x 1 + (5052151777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157316817/5000000000 : ℝ)^523 ≤ (6571693016047/20000000000000 : ℝ)^395 := by
    have hnat : (2157316817 : ℕ)^523*20000000000000^395 ≤ 6571693016047^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157316817 5000000000 6571693016047 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3683207627/10000000000 : ℝ)^523 ≤ (26647810250903/100000000000000 : ℝ)^395 := by
    have hnat : (3683207627 : ℕ)^523*100000000000000^395 ≤ 26647810250903^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683207627 10000000000 26647810250903 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5052151777/10000000000 : ℝ)^523 ≤ (20246862325201/50000000000000 : ℝ)^395 := by
    have hnat : (5052151777 : ℕ)^523*50000000000000^395 ≤ 20246862325201^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052151777 10000000000 20246862325201 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157316817/5000000000 : ℝ), (3683207627/10000000000 : ℝ), (5052151777/10000000000 : ℝ)] ![(6571693016047/20000000000000 : ℝ), (26647810250903/100000000000000 : ℝ), (20246862325201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157316817/5000000000 : ℝ)|^523 ≤ (6571693016047/20000000000000 : ℝ)^395
        have hw : |(2157316817/5000000000 : ℝ)|=(2157316817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3683207627/10000000000 : ℝ)|^523 ≤ (26647810250903/100000000000000 : ℝ)^395
        have hw : |(3683207627/10000000000 : ℝ)|=(3683207627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5052151777/10000000000 : ℝ)|^523 ≤ (20246862325201/50000000000000 : ℝ)^395
        have hw : |(5052151777/10000000000 : ℝ)|=(5052151777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084449807/10000000000 : ℝ)*x 0 + (5018323701/10000000000 : ℝ)*x 1 + (5683373769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084449807/10000000000 : ℝ)^523 ≤ (313509132479/2500000000000 : ℝ)^395 := by
    have hnat : (2084449807 : ℕ)^523*2500000000000^395 ≤ 313509132479^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084449807 10000000000 313509132479 2500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018323701/10000000000 : ℝ)^523 ≤ (20067557861017/50000000000000 : ℝ)^395 := by
    have hnat : (5018323701 : ℕ)^523*50000000000000^395 ≤ 20067557861017^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018323701 10000000000 20067557861017 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5683373769/10000000000 : ℝ)^523 ≤ (11831129743311/25000000000000 : ℝ)^395 := by
    have hnat : (5683373769 : ℕ)^523*25000000000000^395 ≤ 11831129743311^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683373769 10000000000 11831129743311 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084449807/10000000000 : ℝ), (5018323701/10000000000 : ℝ), (5683373769/10000000000 : ℝ)] ![(313509132479/2500000000000 : ℝ), (20067557861017/50000000000000 : ℝ), (11831129743311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084449807/10000000000 : ℝ)|^523 ≤ (313509132479/2500000000000 : ℝ)^395
        have hw : |(-2084449807/10000000000 : ℝ)|=(2084449807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5018323701/10000000000 : ℝ)|^523 ≤ (20067557861017/50000000000000 : ℝ)^395
        have hw : |(5018323701/10000000000 : ℝ)|=(5018323701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5683373769/10000000000 : ℝ)|^523 ≤ (11831129743311/25000000000000 : ℝ)^395
        have hw : |(5683373769/10000000000 : ℝ)|=(5683373769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1310436191/2500000000 : ℝ)*x 0 + (-1777744293/10000000000 : ℝ)*x 1 + (5683376221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310436191/2500000000 : ℝ)^523 ≤ (1062947602871/2500000000000 : ℝ)^395 := by
    have hnat : (1310436191 : ℕ)^523*2500000000000^395 ≤ 1062947602871^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310436191 2500000000 1062947602871 2500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777744293/10000000000 : ℝ)^523 ≤ (5078774929789/50000000000000 : ℝ)^395 := by
    have hnat : (1777744293 : ℕ)^523*50000000000000^395 ≤ 5078774929789^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777744293 10000000000 5078774929789 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5683376221/10000000000 : ℝ)^523 ≤ (23662273003459/50000000000000 : ℝ)^395 := by
    have hnat : (5683376221 : ℕ)^523*50000000000000^395 ≤ 23662273003459^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683376221 10000000000 23662273003459 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310436191/2500000000 : ℝ), (-1777744293/10000000000 : ℝ), (5683376221/10000000000 : ℝ)] ![(1062947602871/2500000000000 : ℝ), (5078774929789/50000000000000 : ℝ), (23662273003459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310436191/2500000000 : ℝ)|^523 ≤ (1062947602871/2500000000000 : ℝ)^395
        have hw : |(1310436191/2500000000 : ℝ)|=(1310436191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777744293/10000000000 : ℝ)|^523 ≤ (5078774929789/50000000000000 : ℝ)^395
        have hw : |(-1777744293/10000000000 : ℝ)|=(1777744293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5683376221/10000000000 : ℝ)|^523 ≤ (23662273003459/50000000000000 : ℝ)^395
        have hw : |(5683376221/10000000000 : ℝ)|=(5683376221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5241744211/10000000000 : ℝ)*x 0 + (568337733/1000000000 : ℝ)*x 1 + (-1777743463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241744211/10000000000 : ℝ)^523 ≤ (4251789817567/10000000000000 : ℝ)^395 := by
    have hnat : (5241744211 : ℕ)^523*10000000000000^395 ≤ 4251789817567^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241744211 10000000000 4251789817567 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568337733/1000000000 : ℝ)^523 ≤ (23662279116907/50000000000000 : ℝ)^395 := by
    have hnat : (568337733 : ℕ)^523*50000000000000^395 ≤ 23662279116907^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568337733 1000000000 23662279116907 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777743463/10000000000 : ℝ)^523 ≤ (10157543580407/100000000000000 : ℝ)^395 := by
    have hnat : (1777743463 : ℕ)^523*100000000000000^395 ≤ 10157543580407^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777743463 10000000000 10157543580407 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241744211/10000000000 : ℝ), (568337733/1000000000 : ℝ), (-1777743463/10000000000 : ℝ)] ![(4251789817567/10000000000000 : ℝ), (23662279116907/50000000000000 : ℝ), (10157543580407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241744211/10000000000 : ℝ)|^523 ≤ (4251789817567/10000000000000 : ℝ)^395
        have hw : |(5241744211/10000000000 : ℝ)|=(5241744211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568337733/1000000000 : ℝ)|^523 ≤ (23662279116907/50000000000000 : ℝ)^395
        have hw : |(568337733/1000000000 : ℝ)|=(568337733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777743463/10000000000 : ℝ)|^523 ≤ (10157543580407/100000000000000 : ℝ)^395
        have hw : |(-1777743463/10000000000 : ℝ)|=(1777743463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s1_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2158076839/5000000000 : ℝ)*x 0 + (1006739653/2000000000 : ℝ)*x 1 + (1851011673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158076839/5000000000 : ℝ)^523 ≤ (328737932001/1000000000000 : ℝ)^395 := by
    have hnat : (2158076839 : ℕ)^523*1000000000000^395 ≤ 328737932001^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158076839 5000000000 328737932001 1000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006739653/2000000000 : ℝ)^523 ≤ (1259312610903/3125000000000 : ℝ)^395 := by
    have hnat : (1006739653 : ℕ)^523*3125000000000^395 ≤ 1259312610903^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006739653 2000000000 1259312610903 3125000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851011673/5000000000 : ℝ)^523 ≤ (13414101618131/50000000000000 : ℝ)^395 := by
    have hnat : (1851011673 : ℕ)^523*50000000000000^395 ≤ 13414101618131^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851011673 5000000000 13414101618131 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158076839/5000000000 : ℝ), (1006739653/2000000000 : ℝ), (1851011673/5000000000 : ℝ)] ![(328737932001/1000000000000 : ℝ), (1259312610903/3125000000000 : ℝ), (13414101618131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158076839/5000000000 : ℝ)|^523 ≤ (328737932001/1000000000000 : ℝ)^395
        have hw : |(2158076839/5000000000 : ℝ)|=(2158076839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006739653/2000000000 : ℝ)|^523 ≤ (1259312610903/3125000000000 : ℝ)^395
        have hw : |(1006739653/2000000000 : ℝ)|=(1006739653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851011673/5000000000 : ℝ)|^523 ≤ (13414101618131/50000000000000 : ℝ)^395
        have hw : |(1851011673/5000000000 : ℝ)|=(1851011673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (549/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (729/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (549/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (549/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (549/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (549/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (549/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (549/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (549/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (3639297993/6250000000000000000 : ℝ) := by
    have hpowers : (549/100000 : ℝ)^8367 ≤ (3639297993/6250000000000000000 : ℝ)^2048 := by
      have hnat : (549 : ℕ)^8367*6250000000000000000^2048 ≤ 3639297993^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        549 100000 3639297993 6250000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (549/100000 : ℝ)) (X := (3639297993/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27689/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (526713775893137563/100000000000000000000 : ℝ) := by
    have hpowers : (27689/100000 : ℝ)^8367 ≤ (526713775893137563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27689 : ℕ)^8367*100000000000000000000^2048 ≤ 526713775893137563^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27689 100000 526713775893137563 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27689/100000 : ℝ)) (X := (526713775893137563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000003639297993/3125000000000000000 : ℝ) ≤ (2000000000570109/2000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (3125000003639297993/3125000000000000000 : ℝ)^2048 ≤ (2000000000570109/2000000000000000 : ℝ)^8367 := by
      have hnat : (3125000003639297993 : ℕ)^2048*2000000000000000^8367 ≤ 2000000000570109^8367*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000003639297993 3125000000000000000 2000000000570109 2000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000570109/2000000000000000 : ℝ)) (X := (3125000003639297993/3125000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100526713834121905451/100000000000000000000 : ℝ) ≤ (5006433435058657/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (100526713834121905451/100000000000000000000 : ℝ)^2048 ≤ (5006433435058657/5000000000000000 : ℝ)^8367 := by
      have hnat : (100526713834121905451 : ℕ)^2048*5000000000000000^8367 ≤ 5006433435058657^8367*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100526713834121905451 100000000000000000000 5006433435058657 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006433435058657/5000000000000000 : ℝ)) (X := (100526713834121905451/100000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50526713775893137563/50000000000000000000 : ℝ) ≤ (10025733737384083/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50526713775893137563/50000000000000000000 : ℝ)^2048 ≤ (10025733737384083/10000000000000000 : ℝ)^8367 := by
      have hnat : (50526713775893137563 : ℕ)^2048*10000000000000000^8367 ≤ 10025733737384083^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50526713775893137563 50000000000000000000 10025733737384083 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025733737384083/10000000000000000 : ℝ)) (X := (50526713775893137563/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3639297993/6250000000000000000 : ℝ) ≤ ((135692936128552439469/135700000000000000000 : ℝ)+2*(12866867266769/2714000000000000 : ℝ)*(549/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (135692936128552439469/135700000000000000000 : ℝ)+2*(12866867266769/2714000000000000 : ℝ)*(549/100000 : ℝ)=(2000000000570109/2000000000000000 : ℝ) by norm_num, show 1+2*(3639297993/6250000000000000000 : ℝ)=(3125000003639297993/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(526713775893137563/100000000000000000000 : ℝ)+(3639297993/6250000000000000000 : ℝ) ≤ ((135692936128552439469/135700000000000000000 : ℝ)+(12866867266769/2714000000000000 : ℝ)*((27689/100000 : ℝ)+(549/100000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (135692936128552439469/135700000000000000000 : ℝ)+(12866867266769/2714000000000000 : ℝ)*((27689/100000 : ℝ)+(549/100000 : ℝ))=(5006433435058657/5000000000000000 : ℝ) by norm_num, show 1+(526713775893137563/100000000000000000000 : ℝ)+(3639297993/6250000000000000000 : ℝ)=(100526713834121905451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(526713775893137563/100000000000000000000 : ℝ) ≤ ((135692936128552439469/135700000000000000000 : ℝ)+2*(12866867266769/2714000000000000 : ℝ)*(27689/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (135692936128552439469/135700000000000000000 : ℝ)+2*(12866867266769/2714000000000000 : ℝ)*(27689/100000 : ℝ)=(10025733737384083/10000000000000000 : ℝ) by norm_num, show 1+2*(526713775893137563/100000000000000000000 : ℝ)=(50526713775893137563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (135692936128552439469/135700000000000000000 : ℝ)*(X 1 0+X 2 0)+(12866867266769/2714000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (549/100000 : ℝ)) (hi := (27689/100000 : ℝ)) (c := (135692936128552439469/135700000000000000000 : ℝ)) (alpha := (12866867266769/2714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (135692936128552439469/135700000000000000000 : ℝ)*(X 0 1+X 2 1)+(12866867266769/2714000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (549/100000 : ℝ)) (hi := (27689/100000 : ℝ)) (c := (135692936128552439469/135700000000000000000 : ℝ)) (alpha := (12866867266769/2714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (135692936128552439469/135700000000000000000 : ℝ)*(X 0 2+X 1 2)+(12866867266769/2714000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (549/100000 : ℝ)) (hi := (27689/100000 : ℝ)) (c := (135692936128552439469/135700000000000000000 : ℝ)) (alpha := (12866867266769/2714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416736993/2000000000 : ℝ)*X 0 0+(2846387203/5000000000 : ℝ)*X 0 1+(1252276537/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677164041/1250000000 : ℝ)*X 1 0+(-1226007709/5000000000 : ℝ)*X 1 1+(1252276299/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417314433/10000000000 : ℝ)*X 2 0+(5009103213/10000000000 : ℝ)*X 2 1+(-613003799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157316817/5000000000 : ℝ)*X 0 0+(3683207627/10000000000 : ℝ)*X 0 1+(5052151777/10000000000 : ℝ)*X 0 2+(2157316817/5000000000 : ℝ)*X 1 0+(3683207627/10000000000 : ℝ)*X 1 1+(5052151777/10000000000 : ℝ)*X 1 2+(2157316817/5000000000 : ℝ)*X 2 0+(3683207627/10000000000 : ℝ)*X 2 1+(5052151777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2084449807/10000000000 : ℝ)*X 0 0+(5018323701/10000000000 : ℝ)*X 0 1+(5683373769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310436191/2500000000 : ℝ)*X 1 0+(-1777744293/10000000000 : ℝ)*X 1 1+(5683376221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5241744211/10000000000 : ℝ)*X 2 0+(568337733/1000000000 : ℝ)*X 2 1+(-1777743463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158076839/5000000000 : ℝ)*X 0 0+(1006739653/2000000000 : ℝ)*X 0 1+(1851011673/5000000000 : ℝ)*X 0 2+(2158076839/5000000000 : ℝ)*X 1 0+(1006739653/2000000000 : ℝ)*X 1 1+(1851011673/5000000000 : ℝ)*X 1 2+(2158076839/5000000000 : ℝ)*X 2 0+(1006739653/2000000000 : ℝ)*X 2 1+(1851011673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (494328778965953084134701/67850000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812601037/100000000000000 : ℝ)*(base1) + (1316880797/100000000000000 : ℝ)*(base19) + (78285057/4000000000000 : ℝ)*(base23) + (8666983/6250000000000 : ℝ)*(base37) + (110874103/100000000000000 : ℝ)*(upper3) + (548297554648369/50000000000000 : ℝ)*(major0) + (548297554648369/50000000000000 : ℝ)*(major1) + (548297554648369/50000000000000 : ℝ)*(major2) + (1462699741029919/100000000000000 : ℝ)*(sp0) + (1462697612710393/100000000000000 : ℝ)*(sp1) + (146269919057799/10000000000000 : ℝ)*(sp2) + (182621969190639/25000000000000 : ℝ)*(sp3) + (554818883/25000000000000 : ℝ)*(sp4) + (277264153/12500000000000 : ℝ)*(sp5) + (18262220700883/2500000000000 : ℝ)*(f.failure) + (731350573852207/50000000000000 : ℝ)*(f.sum) + (143132574041511/67850000000000000000000000000 : ℝ)*base65 + (13393427863410126061/6785000000000000000000000000000000 : ℝ)*base67 + (9612284872679873939/6785000000000000000000000000000000 : ℝ)*base70 + (15264453451900126061/6785000000000000000000000000000000 : ℝ)*base71 + (158614155447661/67850000000000000000000000000 : ℝ)*base73 + (3146321321900126061/6785000000000000000000000000000000 : ℝ)*base75 + (8383616647649873939/6785000000000000000000000000000000 : ℝ)*base78 + (32660742267429873939/6785000000000000000000000000000000 : ℝ)*base80 + (18111646549561/67850000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (263849/50000000000000000000 : ℝ)*base90 + (263849/50000000000000000000 : ℝ)*base92 + (263849/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51022112296733041014805863/57500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18459249/1250000000000 : ℝ)*(base19) + (524792337/25000000000000 : ℝ)*(base23) + (309122273/100000000000000 : ℝ)*(upper2) + (217690093/50000000000000 : ℝ)*(upper3) + (89757527/50000000000000 : ℝ)*(upper5) + (563644107995977/50000000000000 : ℝ)*(major0) + (563644107995977/50000000000000 : ℝ)*(major1) + (563644107995977/50000000000000 : ℝ)*(major2) + (8464931379/100000000000000 : ℝ)*(sp1) + (14177082269/100000000000000 : ℝ)*(sp2) + (375910396343453/25000000000000 : ℝ)*(sp4) + (1503631643702513/100000000000000 : ℝ)*(sp5) + (751812654561097/50000000000000 : ℝ)*(sp6) + (750934817032053/100000000000000 : ℝ)*(sp7) + (750934817032053/100000000000000 : ℝ)*(f.failure) + (375910396343453/25000000000000 : ℝ)*(f.sum) + (189119183585813/67850000000000000000000000000 : ℝ)*base65 + (103085096732141333787/6785000000000000000000000000000000 : ℝ)*base68 + (22895492085706333787/6785000000000000000000000000000000 : ℝ)*base70 + (63781402791126333787/6785000000000000000000000000000000 : ℝ)*base72 + (217057490816587/67850000000000000000000000000 : ℝ)*base74 + (49588708174471333787/6785000000000000000000000000000000 : ℝ)*base76 + (18668447799221333787/6785000000000000000000000000000000 : ℝ)*base78 + (24978715034566333787/6785000000000000000000000000000000 : ℝ)*base80 + (236556840701113/67850000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15354641/2000000000000000000000 : ℝ)*base89 + (15354641/2000000000000000000000 : ℝ)*base91 + (15354641/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (549/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (729/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s2_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-106758371/500000000 : ℝ)*x 0 + (5504639007/10000000000 : ℝ)*x 1 + (206578899/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106758371/500000000 : ℝ)^523 ≤ (64729750373/500000000000 : ℝ)^395 := by
    have hnat : (106758371 : ℕ)^523*500000000000^395 ≤ 64729750373^395*500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106758371 500000000 64729750373 500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504639007/10000000000 : ℝ)^523 ≤ (9072810844767/20000000000000 : ℝ)^395 := by
    have hnat : (5504639007 : ℕ)^523*20000000000000^395 ≤ 9072810844767^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504639007 10000000000 9072810844767 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206578899/400000000 : ℝ)^523 ≤ (5211249460063/12500000000000 : ℝ)^395 := by
    have hnat : (206578899 : ℕ)^523*12500000000000^395 ≤ 5211249460063^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206578899 400000000 5211249460063 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106758371/500000000 : ℝ), (5504639007/10000000000 : ℝ), (206578899/400000000 : ℝ)] ![(64729750373/500000000000 : ℝ), (9072810844767/20000000000000 : ℝ), (5211249460063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106758371/500000000 : ℝ)|^523 ≤ (64729750373/500000000000 : ℝ)^395
        have hw : |(-106758371/500000000 : ℝ)|=(106758371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504639007/10000000000 : ℝ)|^523 ≤ (9072810844767/20000000000000 : ℝ)^395
        have hw : |(5504639007/10000000000 : ℝ)|=(5504639007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206578899/400000000 : ℝ)|^523 ≤ (5211249460063/12500000000000 : ℝ)^395
        have hw : |(206578899/400000000 : ℝ)|=(206578899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2686228701/5000000000 : ℝ)*x 0 + (-288974499/1250000000 : ℝ)*x 1 + (2582237789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686228701/5000000000 : ℝ)^523 ≤ (43927386398583/100000000000000 : ℝ)^395 := by
    have hnat : (2686228701 : ℕ)^523*100000000000000^395 ≤ 43927386398583^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686228701 5000000000 43927386398583 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288974499/1250000000 : ℝ)^523 ≤ (3595646184621/25000000000000 : ℝ)^395 := by
    have hnat : (288974499 : ℕ)^523*25000000000000^395 ≤ 3595646184621^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288974499 1250000000 3595646184621 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582237789/5000000000 : ℝ)^523 ≤ (41690028846443/100000000000000 : ℝ)^395 := by
    have hnat : (2582237789 : ℕ)^523*100000000000000^395 ≤ 41690028846443^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582237789 5000000000 41690028846443 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686228701/5000000000 : ℝ), (-288974499/1250000000 : ℝ), (2582237789/5000000000 : ℝ)] ![(43927386398583/100000000000000 : ℝ), (3595646184621/25000000000000 : ℝ), (41690028846443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686228701/5000000000 : ℝ)|^523 ≤ (43927386398583/100000000000000 : ℝ)^395
        have hw : |(2686228701/5000000000 : ℝ)|=(2686228701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288974499/1250000000 : ℝ)|^523 ≤ (3595646184621/25000000000000 : ℝ)^395
        have hw : |(-288974499/1250000000 : ℝ)|=(288974499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582237789/5000000000 : ℝ)|^523 ≤ (41690028846443/100000000000000 : ℝ)^395
        have hw : |(2582237789/5000000000 : ℝ)|=(2582237789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2686229109/5000000000 : ℝ)*x 0 + (2582237161/5000000000 : ℝ)*x 1 + (-2311796549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686229109/5000000000 : ℝ)^523 ≤ (21963697616289/50000000000000 : ℝ)^395 := by
    have hnat : (2686229109 : ℕ)^523*50000000000000^395 ≤ 21963697616289^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686229109 5000000000 21963697616289 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582237161/5000000000 : ℝ)^523 ≤ (41690015421879/100000000000000 : ℝ)^395 := by
    have hnat : (2582237161 : ℕ)^523*100000000000000^395 ≤ 41690015421879^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582237161 5000000000 41690015421879 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2311796549/10000000000 : ℝ)^523 ≤ (2876517865347/20000000000000 : ℝ)^395 := by
    have hnat : (2311796549 : ℕ)^523*20000000000000^395 ≤ 2876517865347^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311796549 10000000000 2876517865347 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686229109/5000000000 : ℝ), (2582237161/5000000000 : ℝ), (-2311796549/10000000000 : ℝ)] ![(21963697616289/50000000000000 : ℝ), (41690015421879/100000000000000 : ℝ), (2876517865347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686229109/5000000000 : ℝ)|^523 ≤ (21963697616289/50000000000000 : ℝ)^395
        have hw : |(2686229109/5000000000 : ℝ)|=(2686229109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582237161/5000000000 : ℝ)|^523 ≤ (41690015421879/100000000000000 : ℝ)^395
        have hw : |(2582237161/5000000000 : ℝ)|=(2582237161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2311796549/10000000000 : ℝ)|^523 ≤ (2876517865347/20000000000000 : ℝ)^395
        have hw : |(-2311796549/10000000000 : ℝ)|=(2311796549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4350028513/10000000000 : ℝ)*x 0 + (6285273/15625000 : ℝ)*x 1 + (587963233/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350028513/10000000000 : ℝ)^523 ≤ (33215840087701/100000000000000 : ℝ)^395 := by
    have hnat : (4350028513 : ℕ)^523*100000000000000^395 ≤ 33215840087701^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350028513 10000000000 33215840087701 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6285273/15625000 : ℝ)^523 ≤ (14973158918741/50000000000000 : ℝ)^395 := by
    have hnat : (6285273 : ℕ)^523*50000000000000^395 ≤ 14973158918741^395*15625000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6285273 15625000 14973158918741 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587963233/1250000000 : ℝ)^523 ≤ (36837842062757/100000000000000 : ℝ)^395 := by
    have hnat : (587963233 : ℕ)^523*100000000000000^395 ≤ 36837842062757^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587963233 1250000000 36837842062757 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350028513/10000000000 : ℝ), (6285273/15625000 : ℝ), (587963233/1250000000 : ℝ)] ![(33215840087701/100000000000000 : ℝ), (14973158918741/50000000000000 : ℝ), (36837842062757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350028513/10000000000 : ℝ)|^523 ≤ (33215840087701/100000000000000 : ℝ)^395
        have hw : |(4350028513/10000000000 : ℝ)|=(4350028513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6285273/15625000 : ℝ)|^523 ≤ (14973158918741/50000000000000 : ℝ)^395
        have hw : |(6285273/15625000 : ℝ)|=(6285273/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587963233/1250000000 : ℝ)|^523 ≤ (36837842062757/100000000000000 : ℝ)^395
        have hw : |(587963233/1250000000 : ℝ)|=(587963233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-427052103/2000000000 : ℝ)*x 0 + (2583382623/5000000000 : ℝ)*x 1 + (550232433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427052103/2000000000 : ℝ)^523 ≤ (12946697445203/100000000000000 : ℝ)^395 := by
    have hnat : (427052103 : ℕ)^523*100000000000000^395 ≤ 12946697445203^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427052103 2000000000 12946697445203 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583382623/5000000000 : ℝ)^523 ≤ (41714503371239/100000000000000 : ℝ)^395 := by
    have hnat : (2583382623 : ℕ)^523*100000000000000^395 ≤ 41714503371239^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583382623 5000000000 41714503371239 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550232433/1000000000 : ℝ)^523 ≤ (45338799163269/100000000000000 : ℝ)^395 := by
    have hnat : (550232433 : ℕ)^523*100000000000000^395 ≤ 45338799163269^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550232433 1000000000 45338799163269 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427052103/2000000000 : ℝ), (2583382623/5000000000 : ℝ), (550232433/1000000000 : ℝ)] ![(12946697445203/100000000000000 : ℝ), (41714503371239/100000000000000 : ℝ), (45338799163269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427052103/2000000000 : ℝ)|^523 ≤ (12946697445203/100000000000000 : ℝ)^395
        have hw : |(-427052103/2000000000 : ℝ)|=(427052103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583382623/5000000000 : ℝ)|^523 ≤ (41714503371239/100000000000000 : ℝ)^395
        have hw : |(2583382623/5000000000 : ℝ)|=(2583382623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550232433/1000000000 : ℝ)|^523 ≤ (45338799163269/100000000000000 : ℝ)^395
        have hw : |(550232433/1000000000 : ℝ)|=(550232433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (26429801/50000000 : ℝ)*x 0 + (-1973945951/10000000000 : ℝ)*x 1 + (5502324331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26429801/50000000 : ℝ)^523 ≤ (8598684325537/20000000000000 : ℝ)^395 := by
    have hnat : (26429801 : ℕ)^523*20000000000000^395 ≤ 8598684325537^395*50000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26429801 50000000 8598684325537 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973945951/10000000000 : ℝ)^523 ≤ (5833889587307/50000000000000 : ℝ)^395 := by
    have hnat : (1973945951 : ℕ)^523*50000000000000^395 ≤ 5833889587307^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973945951 10000000000 5833889587307 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502324331/10000000000 : ℝ)^523 ≤ (45338799174179/100000000000000 : ℝ)^395 := by
    have hnat : (5502324331 : ℕ)^523*100000000000000^395 ≤ 45338799174179^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502324331 10000000000 45338799174179 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26429801/50000000 : ℝ), (-1973945951/10000000000 : ℝ), (5502324331/10000000000 : ℝ)] ![(8598684325537/20000000000000 : ℝ), (5833889587307/50000000000000 : ℝ), (45338799174179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26429801/50000000 : ℝ)|^523 ≤ (8598684325537/20000000000000 : ℝ)^395
        have hw : |(26429801/50000000 : ℝ)|=(26429801/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973945951/10000000000 : ℝ)|^523 ≤ (5833889587307/50000000000000 : ℝ)^395
        have hw : |(-1973945951/10000000000 : ℝ)|=(1973945951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502324331/10000000000 : ℝ)|^523 ≤ (45338799174179/100000000000000 : ℝ)^395
        have hw : |(5502324331/10000000000 : ℝ)|=(5502324331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (264298017/500000000 : ℝ)*x 0 + (5502324331/10000000000 : ℝ)*x 1 + (-12337161/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264298017/500000000 : ℝ)^523 ≤ (42993423135371/100000000000000 : ℝ)^395 := by
    have hnat : (264298017 : ℕ)^523*100000000000000^395 ≤ 42993423135371^395*500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264298017 500000000 42993423135371 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502324331/10000000000 : ℝ)^523 ≤ (45338799174179/100000000000000 : ℝ)^395 := by
    have hnat : (5502324331 : ℕ)^523*100000000000000^395 ≤ 45338799174179^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502324331 10000000000 45338799174179 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12337161/62500000 : ℝ)^523 ≤ (11667777679787/100000000000000 : ℝ)^395 := by
    have hnat : (12337161 : ℕ)^523*100000000000000^395 ≤ 11667777679787^395*62500000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12337161 62500000 11667777679787 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264298017/500000000 : ℝ), (5502324331/10000000000 : ℝ), (-12337161/62500000 : ℝ)] ![(42993423135371/100000000000000 : ℝ), (45338799174179/100000000000000 : ℝ), (11667777679787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264298017/500000000 : ℝ)|^523 ≤ (42993423135371/100000000000000 : ℝ)^395
        have hw : |(264298017/500000000 : ℝ)|=(264298017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502324331/10000000000 : ℝ)|^523 ≤ (45338799174179/100000000000000 : ℝ)^395
        have hw : |(5502324331/10000000000 : ℝ)|=(5502324331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12337161/62500000 : ℝ)|^523 ≤ (11667777679787/100000000000000 : ℝ)^395
        have hw : |(-12337161/62500000 : ℝ)|=(12337161/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s2_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4350216681/10000000000 : ℝ)*x 0 + (587389681/1250000000 : ℝ)*x 1 + (4027207093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350216681/10000000000 : ℝ)^523 ≤ (6643548501663/20000000000000 : ℝ)^395 := by
    have hnat : (4350216681 : ℕ)^523*20000000000000^395 ≤ 6643548501663^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350216681 10000000000 6643548501663 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587389681/1250000000 : ℝ)^523 ≤ (36790269916923/100000000000000 : ℝ)^395 := by
    have hnat : (587389681 : ℕ)^523*100000000000000^395 ≤ 36790269916923^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587389681 1250000000 36790269916923 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027207093/10000000000 : ℝ)^523 ≤ (29991987565997/100000000000000 : ℝ)^395 := by
    have hnat : (4027207093 : ℕ)^523*100000000000000^395 ≤ 29991987565997^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027207093 10000000000 29991987565997 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350216681/10000000000 : ℝ), (587389681/1250000000 : ℝ), (4027207093/10000000000 : ℝ)] ![(6643548501663/20000000000000 : ℝ), (36790269916923/100000000000000 : ℝ), (29991987565997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350216681/10000000000 : ℝ)|^523 ≤ (6643548501663/20000000000000 : ℝ)^395
        have hw : |(4350216681/10000000000 : ℝ)|=(4350216681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(587389681/1250000000 : ℝ)|^523 ≤ (36790269916923/100000000000000 : ℝ)^395
        have hw : |(587389681/1250000000 : ℝ)|=(587389681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027207093/10000000000 : ℝ)|^523 ≤ (29991987565997/100000000000000 : ℝ)^395
        have hw : |(4027207093/10000000000 : ℝ)|=(4027207093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (729/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8203/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (729/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (729/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (729/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (729/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (729/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (729/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (729/12500 : ℝ) ^ (8367/2048 : ℝ) ≤ (907423729650321/100000000000000000000 : ℝ) := by
    have hpowers : (729/12500 : ℝ)^8367 ≤ (907423729650321/100000000000000000000 : ℝ)^2048 := by
      have hnat : (729 : ℕ)^8367*100000000000000000000^2048 ≤ 907423729650321^2048*12500^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        729 12500 907423729650321 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (729/12500 : ℝ)) (X := (907423729650321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20289/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (36964815283118931/25000000000000000000 : ℝ) := by
    have hpowers : (20289/100000 : ℝ)^8367 ≤ (36964815283118931/25000000000000000000 : ℝ)^2048 := by
      have hnat : (20289 : ℕ)^8367*25000000000000000000^2048 ≤ 36964815283118931^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20289 100000 36964815283118931 25000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20289/100000 : ℝ)) (X := (36964815283118931/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000907423729650321/50000000000000000000 : ℝ) ≤ (5000022210960471/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50000907423729650321/50000000000000000000 : ℝ)^2048 ≤ (5000022210960471/5000000000000000 : ℝ)^8367 := by
      have hnat : (50000907423729650321 : ℕ)^2048*5000000000000000^8367 ≤ 5000022210960471^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000907423729650321 50000000000000000000 5000022210960471 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000022210960471/5000000000000000 : ℝ)) (X := (50000907423729650321/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20029753336972425209/20000000000000000000 : ℝ) ≤ (10003639335057861/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (20029753336972425209/20000000000000000000 : ℝ)^2048 ≤ (10003639335057861/10000000000000000 : ℝ)^8367 := by
      have hnat : (20029753336972425209 : ℕ)^2048*10000000000000000^8367 ≤ 10003639335057861^8367*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20029753336972425209 20000000000000000000 10003639335057861 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003639335057861/10000000000000000 : ℝ)) (X := (20029753336972425209/20000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12536964815283118931/12500000000000000000 : ℝ) ≤ (500361712409739/500000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (12536964815283118931/12500000000000000000 : ℝ)^2048 ≤ (500361712409739/500000000000000 : ℝ)^8367 := by
      have hnat : (12536964815283118931 : ℕ)^2048*500000000000000^8367 ≤ 500361712409739^8367*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12536964815283118931 12500000000000000000 500361712409739 500000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500361712409739/500000000000000 : ℝ)) (X := (12536964815283118931/12500000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(907423729650321/100000000000000000000 : ℝ) ≤ ((24088118523480339213/24095000000000000000 : ℝ)+2*(1198304378973/481900000000000 : ℝ)*(729/12500 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (24088118523480339213/24095000000000000000 : ℝ)+2*(1198304378973/481900000000000 : ℝ)*(729/12500 : ℝ)=(5000022210960471/5000000000000000 : ℝ) by norm_num, show 1+2*(907423729650321/100000000000000000000 : ℝ)=(50000907423729650321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36964815283118931/25000000000000000000 : ℝ)+(907423729650321/100000000000000000000 : ℝ) ≤ ((24088118523480339213/24095000000000000000 : ℝ)+(1198304378973/481900000000000 : ℝ)*((20289/100000 : ℝ)+(729/12500 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (24088118523480339213/24095000000000000000 : ℝ)+(1198304378973/481900000000000 : ℝ)*((20289/100000 : ℝ)+(729/12500 : ℝ))=(10003639335057861/10000000000000000 : ℝ) by norm_num, show 1+(36964815283118931/25000000000000000000 : ℝ)+(907423729650321/100000000000000000000 : ℝ)=(20029753336972425209/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36964815283118931/25000000000000000000 : ℝ) ≤ ((24088118523480339213/24095000000000000000 : ℝ)+2*(1198304378973/481900000000000 : ℝ)*(20289/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (24088118523480339213/24095000000000000000 : ℝ)+2*(1198304378973/481900000000000 : ℝ)*(20289/100000 : ℝ)=(500361712409739/500000000000000 : ℝ) by norm_num, show 1+2*(36964815283118931/25000000000000000000 : ℝ)=(12536964815283118931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24088118523480339213/24095000000000000000 : ℝ)*(X 1 0+X 2 0)+(1198304378973/481900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (729/12500 : ℝ)) (hi := (20289/100000 : ℝ)) (c := (24088118523480339213/24095000000000000000 : ℝ)) (alpha := (1198304378973/481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24088118523480339213/24095000000000000000 : ℝ)*(X 0 1+X 2 1)+(1198304378973/481900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (729/12500 : ℝ)) (hi := (20289/100000 : ℝ)) (c := (24088118523480339213/24095000000000000000 : ℝ)) (alpha := (1198304378973/481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24088118523480339213/24095000000000000000 : ℝ)*(X 0 2+X 1 2)+(1198304378973/481900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (729/12500 : ℝ)) (hi := (20289/100000 : ℝ)) (c := (24088118523480339213/24095000000000000000 : ℝ)) (alpha := (1198304378973/481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106758371/500000000 : ℝ)*X 0 0+(5504639007/10000000000 : ℝ)*X 0 1+(206578899/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686228701/5000000000 : ℝ)*X 1 0+(-288974499/1250000000 : ℝ)*X 1 1+(2582237789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686229109/5000000000 : ℝ)*X 2 0+(2582237161/5000000000 : ℝ)*X 2 1+(-2311796549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350028513/10000000000 : ℝ)*X 0 0+(6285273/15625000 : ℝ)*X 0 1+(587963233/1250000000 : ℝ)*X 0 2+(4350028513/10000000000 : ℝ)*X 1 0+(6285273/15625000 : ℝ)*X 1 1+(587963233/1250000000 : ℝ)*X 1 2+(4350028513/10000000000 : ℝ)*X 2 0+(6285273/15625000 : ℝ)*X 2 1+(587963233/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427052103/2000000000 : ℝ)*X 0 0+(2583382623/5000000000 : ℝ)*X 0 1+(550232433/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26429801/50000000 : ℝ)*X 1 0+(-1973945951/10000000000 : ℝ)*X 1 1+(5502324331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264298017/500000000 : ℝ)*X 2 0+(5502324331/10000000000 : ℝ)*X 2 1+(-12337161/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350216681/10000000000 : ℝ)*X 0 0+(587389681/1250000000 : ℝ)*X 0 1+(4027207093/10000000000 : ℝ)*X 0 2+(4350216681/10000000000 : ℝ)*X 1 0+(587389681/1250000000 : ℝ)*X 1 1+(4027207093/10000000000 : ℝ)*X 1 2+(4350216681/10000000000 : ℝ)*X 2 0+(587389681/1250000000 : ℝ)*X 2 1+(4027207093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98145548705707064067669081/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (568898563/100000000000000 : ℝ)*(base19) + (207941027/25000000000000 : ℝ)*(base23) + (81602457/100000000000000 : ℝ)*(upper2) + (8156643/2000000000000 : ℝ)*(upper3) + (90132819/50000000000000 : ℝ)*(upper4) + (2203974522785947/100000000000000 : ℝ)*(major0) + (2203974522785947/100000000000000 : ℝ)*(major1) + (2203974522785947/100000000000000 : ℝ)*(major2) + (367470527239461/12500000000000 : ℝ)*(sp0) + (734946680138367/25000000000000 : ℝ)*(sp1) + (734946614421981/25000000000000 : ℝ)*(sp2) + (45879734091813/3125000000000 : ℝ)*(sp3) + (2883942043/12500000000000 : ℝ)*(sp4) + (201013121/2000000000000 : ℝ)*(sp7) + (293632308318813/20000000000000 : ℝ)*(f.failure) + (5741772049711/195312500000 : ℝ)*(f.sum) + (147359816042679/24095000000000000000000000000 : ℝ)*base66 + (25247648400449010289/2409500000000000000000000000000000 : ℝ)*base68 + (9216925482672010289/2409500000000000000000000000000000 : ℝ)*base70 + (11266360886372010289/2409500000000000000000000000000000 : ℝ)*base72 + (97775619731649/24095000000000000000000000000 : ℝ)*base74 + (3222251362520010289/2409500000000000000000000000000000 : ℝ)*base76 + (15795713195084010289/2409500000000000000000000000000000 : ℝ)*base78 + (36283989889985010289/2409500000000000000000000000000000 : ℝ)*base80 + (2713580908379/24095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1030361/400000000000000000000 : ℝ)*base89 + (1030361/400000000000000000000 : ℝ)*base91 + (1030361/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14138371347222388324368759/3050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293142213/25000000000000 : ℝ)*(base19) + (665406097/50000000000000 : ℝ)*(base23) + (8591071/50000000000000 : ℝ)*(upper2) + (147757711/100000000000000 : ℝ)*(upper3) + (100785599/100000000000000 : ℝ)*(upper5) + (446839497732133/20000000000000 : ℝ)*(major0) + (446839497732133/20000000000000 : ℝ)*(major1) + (446839497732133/20000000000000 : ℝ)*(major2) + (11245379353/100000000000000 : ℝ)*(sp1) + (14105855453/100000000000000 : ℝ)*(sp2) + (46564069892013/1562500000000 : ℝ)*(sp4) + (745022013785157/25000000000000 : ℝ)*(sp5) + (1490042518210593/50000000000000 : ℝ)*(sp6) + (148829434971477/10000000000000 : ℝ)*(sp7) + (148829434971477/10000000000000 : ℝ)*(f.failure) + (46564069892013/1562500000000 : ℝ)*(f.sum) + (38553567020501/4819000000000000000000000000 : ℝ)*base66 + (2522561099640318671/481900000000000000000000000000000 : ℝ)*base68 + (497475880302518671/481900000000000000000000000000000 : ℝ)*base70 + (3078175050723918671/481900000000000000000000000000000 : ℝ)*base72 + (6149498760791/963800000000000000000000000 : ℝ)*base74 + (699911633312318671/481900000000000000000000000000000 : ℝ)*base76 + (6349263813991118671/481900000000000000000000000000000 : ℝ)*base78 + (4597392035784318671/481900000000000000000000000000000 : ℝ)*base80 + (6421500232749/2409500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1942769/200000000000000000000 : ℝ)*base89 + (1942769/200000000000000000000 : ℝ)*base91 + (1942769/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (729/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1175_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1175_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1175_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1175_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8203/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
