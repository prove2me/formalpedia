-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:45.007041+00:00
-- url     : https://prove2.me/submissions/d9ca28a1-bbf8-4668-83b3-be9a74fd830e

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
theorem support_rectangle_w1410_s6_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986648853/10000000000 : ℝ)*x 0 + (338075393/625000000 : ℝ)*x 1 + (2623229949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986648853/10000000000 : ℝ)^2185 ≤ (6057454547401/50000000000000 : ℝ)^1673 := by
    have hnat : (1986648853 : ℕ)^2185*50000000000000^1673 ≤ 6057454547401^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986648853 10000000000 6057454547401 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338075393/625000000 : ℝ)^2185 ≤ (8963807359141/20000000000000 : ℝ)^1673 := by
    have hnat : (338075393 : ℕ)^2185*20000000000000^1673 ≤ 8963807359141^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338075393 625000000 8963807359141 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623229949/5000000000 : ℝ)^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673 := by
    have hnat : (2623229949 : ℕ)^2185*10000000000000^1673 ≤ 4306605409091^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623229949 5000000000 4306605409091 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986648853/10000000000 : ℝ), (338075393/625000000 : ℝ), (2623229949/5000000000 : ℝ)] ![(6057454547401/50000000000000 : ℝ), (8963807359141/20000000000000 : ℝ), (4306605409091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986648853/10000000000 : ℝ)|^2185 ≤ (6057454547401/50000000000000 : ℝ)^1673
        have hw : |(-1986648853/10000000000 : ℝ)|=(1986648853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338075393/625000000 : ℝ)|^2185 ≤ (8963807359141/20000000000000 : ℝ)^1673
        have hw : |(338075393/625000000 : ℝ)|=(338075393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623229949/5000000000 : ℝ)|^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673
        have hw : |(2623229949/5000000000 : ℝ)|=(2623229949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347722087/10000000000 : ℝ)*x 0 + (-2069519033/10000000000 : ℝ)*x 1 + (2623229949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347722087/10000000000 : ℝ)^2185 ≤ (44154850387153/100000000000000 : ℝ)^1673 := by
    have hnat : (5347722087 : ℕ)^2185*100000000000000^1673 ≤ 44154850387153^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347722087 10000000000 44154850387153 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069519033/10000000000 : ℝ)^2185 ≤ (1277909549673/10000000000000 : ℝ)^1673 := by
    have hnat : (2069519033 : ℕ)^2185*10000000000000^1673 ≤ 1277909549673^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069519033 10000000000 1277909549673 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623229949/5000000000 : ℝ)^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673 := by
    have hnat : (2623229949 : ℕ)^2185*10000000000000^1673 ≤ 4306605409091^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623229949 5000000000 4306605409091 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347722087/10000000000 : ℝ), (-2069519033/10000000000 : ℝ), (2623229949/5000000000 : ℝ)] ![(44154850387153/100000000000000 : ℝ), (1277909549673/10000000000000 : ℝ), (4306605409091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347722087/10000000000 : ℝ)|^2185 ≤ (44154850387153/100000000000000 : ℝ)^1673
        have hw : |(5347722087/10000000000 : ℝ)|=(5347722087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069519033/10000000000 : ℝ)|^2185 ≤ (1277909549673/10000000000000 : ℝ)^1673
        have hw : |(-2069519033/10000000000 : ℝ)|=(2069519033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623229949/5000000000 : ℝ)|^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673
        have hw : |(2623229949/5000000000 : ℝ)|=(2623229949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347722087/10000000000 : ℝ)*x 0 + (2623229949/5000000000 : ℝ)*x 1 + (-2069519033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347722087/10000000000 : ℝ)^2185 ≤ (44154850387153/100000000000000 : ℝ)^1673 := by
    have hnat : (5347722087 : ℕ)^2185*100000000000000^1673 ≤ 44154850387153^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347722087 10000000000 44154850387153 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623229949/5000000000 : ℝ)^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673 := by
    have hnat : (2623229949 : ℕ)^2185*10000000000000^1673 ≤ 4306605409091^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623229949 5000000000 4306605409091 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069519033/10000000000 : ℝ)^2185 ≤ (1277909549673/10000000000000 : ℝ)^1673 := by
    have hnat : (2069519033 : ℕ)^2185*10000000000000^1673 ≤ 1277909549673^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069519033 10000000000 1277909549673 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347722087/10000000000 : ℝ), (2623229949/5000000000 : ℝ), (-2069519033/10000000000 : ℝ)] ![(44154850387153/100000000000000 : ℝ), (4306605409091/10000000000000 : ℝ), (1277909549673/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347722087/10000000000 : ℝ)|^2185 ≤ (44154850387153/100000000000000 : ℝ)^1673
        have hw : |(5347722087/10000000000 : ℝ)|=(5347722087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623229949/5000000000 : ℝ)|^2185 ≤ (4306605409091/10000000000000 : ℝ)^1673
        have hw : |(2623229949/5000000000 : ℝ)|=(2623229949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069519033/10000000000 : ℝ)|^2185 ≤ (1277909549673/10000000000000 : ℝ)^1673
        have hw : |(-2069519033/10000000000 : ℝ)|=(2069519033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077286707/2500000000 : ℝ)*x 0 + (82751001/200000000 : ℝ)*x 1 + (280448469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077286707/2500000000 : ℝ)^2185 ≤ (8326097404523/25000000000000 : ℝ)^1673 := by
    have hnat : (1077286707 : ℕ)^2185*25000000000000^1673 ≤ 8326097404523^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077286707 2500000000 8326097404523 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82751001/200000000 : ℝ)^2185 ≤ (31582935598667/100000000000000 : ℝ)^1673 := by
    have hnat : (82751001 : ℕ)^2185*100000000000000^1673 ≤ 31582935598667^1673*200000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82751001 200000000 31582935598667 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280448469/625000000 : ℝ)^2185 ≤ (8778168689661/25000000000000 : ℝ)^1673 := by
    have hnat : (280448469 : ℕ)^2185*25000000000000^1673 ≤ 8778168689661^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280448469 625000000 8778168689661 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077286707/2500000000 : ℝ), (82751001/200000000 : ℝ), (280448469/625000000 : ℝ)] ![(8326097404523/25000000000000 : ℝ), (31582935598667/100000000000000 : ℝ), (8778168689661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077286707/2500000000 : ℝ)|^2185 ≤ (8326097404523/25000000000000 : ℝ)^1673
        have hw : |(1077286707/2500000000 : ℝ)|=(1077286707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82751001/200000000 : ℝ)|^2185 ≤ (31582935598667/100000000000000 : ℝ)^1673
        have hw : |(82751001/200000000 : ℝ)|=(82751001/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280448469/625000000 : ℝ)|^2185 ≤ (8778168689661/25000000000000 : ℝ)^1673
        have hw : |(280448469/625000000 : ℝ)|=(280448469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986660351/10000000000 : ℝ)*x 0 + (32794037/62500000 : ℝ)*x 1 + (5408617237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986660351/10000000000 : ℝ)^2185 ≤ (3028750167467/25000000000000 : ℝ)^1673 := by
    have hnat : (1986660351 : ℕ)^2185*25000000000000^1673 ≤ 3028750167467^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986660351 10000000000 3028750167467 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32794037/62500000 : ℝ)^2185 ≤ (43072336779983/100000000000000 : ℝ)^1673 := by
    have hnat : (32794037 : ℕ)^2185*100000000000000^1673 ≤ 43072336779983^1673*62500000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32794037 62500000 43072336779983 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408617237/10000000000 : ℝ)^2185 ≤ (22406331265199/50000000000000 : ℝ)^1673 := by
    have hnat : (5408617237 : ℕ)^2185*50000000000000^1673 ≤ 22406331265199^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408617237 10000000000 22406331265199 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986660351/10000000000 : ℝ), (32794037/62500000 : ℝ), (5408617237/10000000000 : ℝ)] ![(3028750167467/25000000000000 : ℝ), (43072336779983/100000000000000 : ℝ), (22406331265199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986660351/10000000000 : ℝ)|^2185 ≤ (3028750167467/25000000000000 : ℝ)^1673
        have hw : |(-1986660351/10000000000 : ℝ)|=(1986660351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32794037/62500000 : ℝ)|^2185 ≤ (43072336779983/100000000000000 : ℝ)^1673
        have hw : |(32794037/62500000 : ℝ)|=(32794037/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408617237/10000000000 : ℝ)|^2185 ≤ (22406331265199/50000000000000 : ℝ)^1673
        have hw : |(5408617237/10000000000 : ℝ)|=(5408617237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326373107/2500000000 : ℝ)*x 0 + (-1907361691/10000000000 : ℝ)*x 1 + (135215431/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326373107/2500000000 : ℝ)^2185 ≤ (21850006266031/50000000000000 : ℝ)^1673 := by
    have hnat : (1326373107 : ℕ)^2185*50000000000000^1673 ≤ 21850006266031^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326373107 2500000000 21850006266031 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907361691/10000000000 : ℝ)^2185 ≤ (2297464977863/20000000000000 : ℝ)^1673 := by
    have hnat : (1907361691 : ℕ)^2185*20000000000000^1673 ≤ 2297464977863^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907361691 10000000000 2297464977863 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135215431/250000000 : ℝ)^2185 ≤ (44812662562861/100000000000000 : ℝ)^1673 := by
    have hnat : (135215431 : ℕ)^2185*100000000000000^1673 ≤ 44812662562861^1673*250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135215431 250000000 44812662562861 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326373107/2500000000 : ℝ), (-1907361691/10000000000 : ℝ), (135215431/250000000 : ℝ)] ![(21850006266031/50000000000000 : ℝ), (2297464977863/20000000000000 : ℝ), (44812662562861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326373107/2500000000 : ℝ)|^2185 ≤ (21850006266031/50000000000000 : ℝ)^1673
        have hw : |(1326373107/2500000000 : ℝ)|=(1326373107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1907361691/10000000000 : ℝ)|^2185 ≤ (2297464977863/20000000000000 : ℝ)^1673
        have hw : |(-1907361691/10000000000 : ℝ)|=(1907361691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135215431/250000000 : ℝ)|^2185 ≤ (44812662562861/100000000000000 : ℝ)^1673
        have hw : |(135215431/250000000 : ℝ)|=(135215431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652746217/5000000000 : ℝ)*x 0 + (5408617231/10000000000 : ℝ)*x 1 + (-381472339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652746217/5000000000 : ℝ)^2185 ≤ (43700012596607/100000000000000 : ℝ)^1673 := by
    have hnat : (2652746217 : ℕ)^2185*100000000000000^1673 ≤ 43700012596607^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652746217 5000000000 43700012596607 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408617231/10000000000 : ℝ)^2185 ≤ (44812662465471/100000000000000 : ℝ)^1673 := by
    have hnat : (5408617231 : ℕ)^2185*100000000000000^1673 ≤ 44812662465471^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408617231 10000000000 44812662465471 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381472339/2000000000 : ℝ)^2185 ≤ (5743662460389/50000000000000 : ℝ)^1673 := by
    have hnat : (381472339 : ℕ)^2185*50000000000000^1673 ≤ 5743662460389^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381472339 2000000000 5743662460389 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652746217/5000000000 : ℝ), (5408617231/10000000000 : ℝ), (-381472339/2000000000 : ℝ)] ![(43700012596607/100000000000000 : ℝ), (44812662465471/100000000000000 : ℝ), (5743662460389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652746217/5000000000 : ℝ)|^2185 ≤ (43700012596607/100000000000000 : ℝ)^1673
        have hw : |(2652746217/5000000000 : ℝ)|=(2652746217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408617231/10000000000 : ℝ)|^2185 ≤ (44812662465471/100000000000000 : ℝ)^1673
        have hw : |(5408617231/10000000000 : ℝ)|=(5408617231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381472339/2000000000 : ℝ)|^2185 ≤ (5743662460389/50000000000000 : ℝ)^1673
        have hw : |(-381472339/2000000000 : ℝ)|=(381472339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s6_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4309171543/10000000000 : ℝ)*x 0 + (56073957/125000000 : ℝ)*x 1 + (4138815501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309171543/10000000000 : ℝ)^2185 ≤ (33304639092891/100000000000000 : ℝ)^1673 := by
    have hnat : (4309171543 : ℕ)^2185*100000000000000^1673 ≤ 33304639092891^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309171543 10000000000 33304639092891 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56073957/125000000 : ℝ)^2185 ≤ (2193738064863/6250000000000 : ℝ)^1673 := by
    have hnat : (56073957 : ℕ)^2185*6250000000000^1673 ≤ 2193738064863^1673*125000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56073957 125000000 2193738064863 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138815501/10000000000 : ℝ)^2185 ≤ (31595551851717/100000000000000 : ℝ)^1673 := by
    have hnat : (4138815501 : ℕ)^2185*100000000000000^1673 ≤ 31595551851717^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138815501 10000000000 31595551851717 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309171543/10000000000 : ℝ), (56073957/125000000 : ℝ), (4138815501/10000000000 : ℝ)] ![(33304639092891/100000000000000 : ℝ), (2193738064863/6250000000000 : ℝ), (31595551851717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309171543/10000000000 : ℝ)|^2185 ≤ (33304639092891/100000000000000 : ℝ)^1673
        have hw : |(4309171543/10000000000 : ℝ)|=(4309171543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56073957/125000000 : ℝ)|^2185 ≤ (2193738064863/6250000000000 : ℝ)^1673
        have hw : |(56073957/125000000 : ℝ)|=(56073957/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138815501/10000000000 : ℝ)|^2185 ≤ (31595551851717/100000000000000 : ℝ)^1673
        have hw : |(4138815501/10000000000 : ℝ)|=(4138815501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/3125 : ℝ) ^ (4369/1024 : ℝ) ≤ (2275867554227519/25000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^4369 ≤ (2275867554227519/25000000000000000000 : ℝ)^1024 := by
      have hnat : (353 : ℕ)^4369*25000000000000000000^1024 ≤ 2275867554227519^1024*3125^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 2275867554227519 25000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (2275867554227519/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (4369/1024 : ℝ) ≤ (28432691120704551/100000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^4369 ≤ (28432691120704551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (461 : ℕ)^4369*100000000000000000000^1024 ≤ 28432691120704551^1024*3125^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 28432691120704551 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (28432691120704551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502275867554227519/12500000000000000000 : ℝ) ≤ (10000426701938619/10000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (12502275867554227519/12500000000000000000 : ℝ)^1024 ≤ (10000426701938619/10000000000000000 : ℝ)^4369 := by
      have hnat : (12502275867554227519 : ℕ)^1024*10000000000000000^4369 ≤ 10000426701938619^4369*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502275867554227519 12500000000000000000 10000426701938619 10000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000426701938619/10000000000000000 : ℝ)) (X := (12502275867554227519/12500000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037536161337614627/100000000000000000000 : ℝ) ≤ (10000879640817551/10000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100037536161337614627/100000000000000000000 : ℝ)^1024 ≤ (10000879640817551/10000000000000000 : ℝ)^4369 := by
      have hnat : (100037536161337614627 : ℕ)^1024*10000000000000000^4369 ≤ 10000879640817551^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037536161337614627 100000000000000000000 10000879640817551 10000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000879640817551/10000000000000000 : ℝ)) (X := (100037536161337614627/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028432691120704551/50000000000000000000 : ℝ) ≤ (10001332579696483/10000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50028432691120704551/50000000000000000000 : ℝ)^1024 ≤ (10001332579696483/10000000000000000 : ℝ)^4369 := by
      have hnat : (50028432691120704551 : ℕ)^1024*10000000000000000^4369 ≤ 10001332579696483^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028432691120704551 50000000000000000000 10001332579696483 10000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001332579696483/10000000000000000 : ℝ)) (X := (50028432691120704551/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2275867554227519/25000000000000000000 : ℝ) ≤ ((53986315448042243/54000000000000000 : ℝ)+2*(113234719733/86400000000000 : ℝ)*(353/3125 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (53986315448042243/54000000000000000 : ℝ)+2*(113234719733/86400000000000 : ℝ)*(353/3125 : ℝ)=(10000426701938619/10000000000000000 : ℝ) by norm_num, show 1+2*(2275867554227519/25000000000000000000 : ℝ)=(12502275867554227519/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28432691120704551/100000000000000000000 : ℝ)+(2275867554227519/25000000000000000000 : ℝ) ≤ ((53986315448042243/54000000000000000 : ℝ)+(113234719733/86400000000000 : ℝ)*((461/3125 : ℝ)+(353/3125 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (53986315448042243/54000000000000000 : ℝ)+(113234719733/86400000000000 : ℝ)*((461/3125 : ℝ)+(353/3125 : ℝ))=(10000879640817551/10000000000000000 : ℝ) by norm_num, show 1+(28432691120704551/100000000000000000000 : ℝ)+(2275867554227519/25000000000000000000 : ℝ)=(100037536161337614627/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28432691120704551/100000000000000000000 : ℝ) ≤ ((53986315448042243/54000000000000000 : ℝ)+2*(113234719733/86400000000000 : ℝ)*(461/3125 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (53986315448042243/54000000000000000 : ℝ)+2*(113234719733/86400000000000 : ℝ)*(461/3125 : ℝ)=(10001332579696483/10000000000000000 : ℝ) by norm_num, show 1+2*(28432691120704551/100000000000000000000 : ℝ)=(50028432691120704551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53986315448042243/54000000000000000 : ℝ)*(X 1 0+X 2 0)+(113234719733/86400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (461/3125 : ℝ)) (c := (53986315448042243/54000000000000000 : ℝ)) (alpha := (113234719733/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53986315448042243/54000000000000000 : ℝ)*(X 0 1+X 2 1)+(113234719733/86400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (461/3125 : ℝ)) (c := (53986315448042243/54000000000000000 : ℝ)) (alpha := (113234719733/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53986315448042243/54000000000000000 : ℝ)*(X 0 2+X 1 2)+(113234719733/86400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (461/3125 : ℝ)) (c := (53986315448042243/54000000000000000 : ℝ)) (alpha := (113234719733/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986648853/10000000000 : ℝ)*X 0 0+(338075393/625000000 : ℝ)*X 0 1+(2623229949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347722087/10000000000 : ℝ)*X 1 0+(-2069519033/10000000000 : ℝ)*X 1 1+(2623229949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347722087/10000000000 : ℝ)*X 2 0+(2623229949/5000000000 : ℝ)*X 2 1+(-2069519033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077286707/2500000000 : ℝ)*X 0 0+(82751001/200000000 : ℝ)*X 0 1+(280448469/625000000 : ℝ)*X 0 2+(1077286707/2500000000 : ℝ)*X 1 0+(82751001/200000000 : ℝ)*X 1 1+(280448469/625000000 : ℝ)*X 1 2+(1077286707/2500000000 : ℝ)*X 2 0+(82751001/200000000 : ℝ)*X 2 1+(280448469/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1986660351/10000000000 : ℝ)*X 0 0+(32794037/62500000 : ℝ)*X 0 1+(5408617237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326373107/2500000000 : ℝ)*X 1 0+(-1907361691/10000000000 : ℝ)*X 1 1+(135215431/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652746217/5000000000 : ℝ)*X 2 0+(5408617231/10000000000 : ℝ)*X 2 1+(-381472339/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309171543/10000000000 : ℝ)*X 0 0+(56073957/125000000 : ℝ)*X 0 1+(4138815501/10000000000 : ℝ)*X 0 2+(4309171543/10000000000 : ℝ)*X 1 0+(56073957/125000000 : ℝ)*X 1 1+(4138815501/10000000000 : ℝ)*X 1 2+(4309171543/10000000000 : ℝ)*X 2 0+(56073957/125000000 : ℝ)*X 2 1+(4138815501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3027510806405751983555299/300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1851317557/100000000000000 : ℝ)*(base19) + (345100659/20000000000000 : ℝ)*(base23) + (67281971/100000000000000 : ℝ)*(lower2) + (252210017/100000000000000 : ℝ)*(upper3) + (80213233/50000000000000 : ℝ)*(upper5) + (4502424805245507/100000000000000 : ℝ)*(major0) + (4502424805245507/100000000000000 : ℝ)*(major1) + (4502424805245507/100000000000000 : ℝ)*(major2) + (614456993667/10000000000 : ℝ)*(sp0) + (3072303401072557/50000000000000 : ℝ)*(sp1) + (384037932997461/6250000000000 : ℝ)*(sp2) + (2860221125183233/100000000000000 : ℝ)*(sp3) + (38716792671/100000000000000 : ℝ)*(sp4) + (1949545501/10000000000000 : ℝ)*(sp7) + (715060155159561/25000000000000 : ℝ)*(f.failure) + (6144608653462671/100000000000000 : ℝ)*(f.sum) + (492960849643/1440000000000000000000000000 : ℝ)*base66 + (2930854708332149/225000000000000000000000000000 : ℝ)*base67 + (2986052856057149/225000000000000000000000000000 : ℝ)*base69 + (142304000382149/225000000000000000000000000000 : ℝ)*base71 + (4439896447157/1440000000000000000000000000 : ℝ)*base73 + (1952828478432149/225000000000000000000000000000 : ℝ)*base75 + (646977921732149/225000000000000000000000000000 : ℝ)*base77 + (6188924159532149/225000000000000000000000000000 : ℝ)*base79 + (5619100140917/1440000000000000000000000000 : ℝ)*base81 + (26687517/2500000000000000000000 : ℝ)*base89 + (26687517/2500000000000000000000 : ℝ)*base91 + (26687517/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4325192245982170942852609/900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (815791661/100000000000000 : ℝ)*(base19) + (112660809/12500000000000 : ℝ)*(base23) + (27961113/10000000000000 : ℝ)*(lower1) + (96806807/100000000000000 : ℝ)*(upper3) + (9079961/25000000000000 : ℝ)*(lower4) + (1558631/1562500000000 : ℝ)*(upper5) + (4535098286630971/100000000000000 : ℝ)*(major0) + (4535098286630971/100000000000000 : ℝ)*(major1) + (4535098286630971/100000000000000 : ℝ)*(major2) + (1261157849/100000000000000 : ℝ)*(sp2) + (618919941720717/10000000000000 : ℝ)*(sp4) + (6189198601415509/100000000000000 : ℝ)*(sp5) + (6189197254762849/100000000000000 : ℝ)*(sp6) + (2880996995862433/100000000000000 : ℝ)*(sp7) + (2880996995862433/100000000000000 : ℝ)*(f.failure) + (618919941720717/10000000000000 : ℝ)*(f.sum) + (4529256071063/4320000000000000000000000000 : ℝ)*base65 + (52028419729397209/675000000000000000000000000000 : ℝ)*base68 + (9097155010922209/675000000000000000000000000000 : ℝ)*base70 + (128588386565822209/675000000000000000000000000000 : ℝ)*base72 + (22264668316777/4320000000000000000000000000 : ℝ)*base74 + (6612335473172209/675000000000000000000000000000 : ℝ)*base76 + (5092566462797209/675000000000000000000000000000 : ℝ)*base78 + (13285609511072209/675000000000000000000000000000 : ℝ)*base80 + (1440294451223/4320000000000000000000000000 : ℝ)*base81 + (113161301/10000000000000000000000 : ℝ)*base89 + (113161301/10000000000000000000000 : ℝ)*base91 + (113161301/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1410_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_s7_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986654399/10000000000 : ℝ)*x 0 + (5409171661/10000000000 : ℝ)*x 1 + (5246490731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986654399/10000000000 : ℝ)^2185 ≤ (2422990653107/20000000000000 : ℝ)^1673 := by
    have hnat : (1986654399 : ℕ)^2185*20000000000000^1673 ≤ 2422990653107^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986654399 10000000000 2422990653107 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409171661/10000000000 : ℝ)^2185 ≤ (4481866208257/10000000000000 : ℝ)^1673 := by
    have hnat : (5409171661 : ℕ)^2185*10000000000000^1673 ≤ 4481866208257^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409171661 10000000000 4481866208257 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246490731/10000000000 : ℝ)^2185 ≤ (43066384643373/100000000000000 : ℝ)^1673 := by
    have hnat : (5246490731 : ℕ)^2185*100000000000000^1673 ≤ 43066384643373^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246490731 10000000000 43066384643373 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986654399/10000000000 : ℝ), (5409171661/10000000000 : ℝ), (5246490731/10000000000 : ℝ)] ![(2422990653107/20000000000000 : ℝ), (4481866208257/10000000000000 : ℝ), (43066384643373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986654399/10000000000 : ℝ)|^2185 ≤ (2422990653107/20000000000000 : ℝ)^1673
        have hw : |(-1986654399/10000000000 : ℝ)|=(1986654399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409171661/10000000000 : ℝ)|^2185 ≤ (4481866208257/10000000000000 : ℝ)^1673
        have hw : |(5409171661/10000000000 : ℝ)|=(5409171661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246490731/10000000000 : ℝ)|^2185 ≤ (43066384643373/100000000000000 : ℝ)^1673
        have hw : |(5246490731/10000000000 : ℝ)|=(5246490731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673856311/5000000000 : ℝ)*x 0 + (-517372673/2500000000 : ℝ)*x 1 + (5246490739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673856311/5000000000 : ℝ)^2185 ≤ (44154748320097/100000000000000 : ℝ)^1673 := by
    have hnat : (2673856311 : ℕ)^2185*100000000000000^1673 ≤ 44154748320097^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673856311 5000000000 44154748320097 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517372673/2500000000 : ℝ)^2185 ≤ (12778866936613/100000000000000 : ℝ)^1673 := by
    have hnat : (517372673 : ℕ)^2185*100000000000000^1673 ≤ 12778866936613^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517372673 2500000000 12778866936613 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246490739/10000000000 : ℝ)^2185 ≤ (43066384729139/100000000000000 : ℝ)^1673 := by
    have hnat : (5246490739 : ℕ)^2185*100000000000000^1673 ≤ 43066384729139^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246490739 10000000000 43066384729139 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673856311/5000000000 : ℝ), (-517372673/2500000000 : ℝ), (5246490739/10000000000 : ℝ)] ![(44154748320097/100000000000000 : ℝ), (12778866936613/100000000000000 : ℝ), (43066384729139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673856311/5000000000 : ℝ)|^2185 ≤ (44154748320097/100000000000000 : ℝ)^1673
        have hw : |(2673856311/5000000000 : ℝ)|=(2673856311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517372673/2500000000 : ℝ)|^2185 ≤ (12778866936613/100000000000000 : ℝ)^1673
        have hw : |(-517372673/2500000000 : ℝ)|=(517372673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246490739/10000000000 : ℝ)|^2185 ≤ (43066384729139/100000000000000 : ℝ)^1673
        have hw : |(5246490739/10000000000 : ℝ)|=(5246490739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668464079/1250000000 : ℝ)*x 0 + (5246490691/10000000000 : ℝ)*x 1 + (-1034745371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668464079/1250000000 : ℝ)^2185 ≤ (44154748427933/100000000000000 : ℝ)^1673 := by
    have hnat : (668464079 : ℕ)^2185*100000000000000^1673 ≤ 44154748427933^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668464079 1250000000 44154748427933 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246490691/10000000000 : ℝ)^2185 ≤ (43066384214543/100000000000000 : ℝ)^1673 := by
    have hnat : (5246490691 : ℕ)^2185*100000000000000^1673 ≤ 43066384214543^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246490691 10000000000 43066384214543 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034745371/5000000000 : ℝ)^2185 ≤ (3194716834961/25000000000000 : ℝ)^1673 := by
    have hnat : (1034745371 : ℕ)^2185*25000000000000^1673 ≤ 3194716834961^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034745371 5000000000 3194716834961 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668464079/1250000000 : ℝ), (5246490691/10000000000 : ℝ), (-1034745371/5000000000 : ℝ)] ![(44154748427933/100000000000000 : ℝ), (43066384214543/100000000000000 : ℝ), (3194716834961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668464079/1250000000 : ℝ)|^2185 ≤ (44154748427933/100000000000000 : ℝ)^1673
        have hw : |(668464079/1250000000 : ℝ)|=(668464079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246490691/10000000000 : ℝ)|^2185 ≤ (43066384214543/100000000000000 : ℝ)^1673
        have hw : |(5246490691/10000000000 : ℝ)|=(5246490691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034745371/5000000000 : ℝ)|^2185 ≤ (3194716834961/25000000000000 : ℝ)^1673
        have hw : |(-1034745371/5000000000 : ℝ)|=(1034745371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4309149223/10000000000 : ℝ)*x 0 + (258601243/625000000 : ℝ)*x 1 + (4487105013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309149223/10000000000 : ℝ)^2185 ≤ (8326103448339/25000000000000 : ℝ)^1673 := by
    have hnat : (4309149223 : ℕ)^2185*25000000000000^1673 ≤ 8326103448339^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309149223 10000000000 8326103448339 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258601243/625000000 : ℝ)^2185 ≤ (31583631836551/100000000000000 : ℝ)^1673 := by
    have hnat : (258601243 : ℕ)^2185*100000000000000^1673 ≤ 31583631836551^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258601243 625000000 31583631836551 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487105013/10000000000 : ℝ)^2185 ≤ (35111954349883/100000000000000 : ℝ)^1673 := by
    have hnat : (4487105013 : ℕ)^2185*100000000000000^1673 ≤ 35111954349883^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487105013 10000000000 35111954349883 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309149223/10000000000 : ℝ), (258601243/625000000 : ℝ), (4487105013/10000000000 : ℝ)] ![(8326103448339/25000000000000 : ℝ), (31583631836551/100000000000000 : ℝ), (35111954349883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309149223/10000000000 : ℝ)|^2185 ≤ (8326103448339/25000000000000 : ℝ)^1673
        have hw : |(4309149223/10000000000 : ℝ)|=(4309149223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258601243/625000000 : ℝ)|^2185 ≤ (31583631836551/100000000000000 : ℝ)^1673
        have hw : |(258601243/625000000 : ℝ)|=(258601243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487105013/10000000000 : ℝ)|^2185 ≤ (35111954349883/100000000000000 : ℝ)^1673
        have hw : |(4487105013/10000000000 : ℝ)|=(4487105013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-496666489/2500000000 : ℝ)*x 0 + (209883049/400000000 : ℝ)*x 1 + (5408583087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496666489/2500000000 : ℝ)^2185 ≤ (12115045310581/100000000000000 : ℝ)^1673 := by
    have hnat : (496666489 : ℕ)^2185*100000000000000^1673 ≤ 12115045310581^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496666489 2500000000 12115045310581 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209883049/400000000 : ℝ)^2185 ≤ (21536330841499/50000000000000 : ℝ)^1673 := by
    have hnat : (209883049 : ℕ)^2185*50000000000000^1673 ≤ 21536330841499^1673*400000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209883049 400000000 21536330841499 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408583087/10000000000 : ℝ)^2185 ≤ (44812292991389/100000000000000 : ℝ)^1673 := by
    have hnat : (5408583087 : ℕ)^2185*100000000000000^1673 ≤ 44812292991389^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408583087 10000000000 44812292991389 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496666489/2500000000 : ℝ), (209883049/400000000 : ℝ), (5408583087/10000000000 : ℝ)] ![(12115045310581/100000000000000 : ℝ), (21536330841499/50000000000000 : ℝ), (44812292991389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496666489/2500000000 : ℝ)|^2185 ≤ (12115045310581/100000000000000 : ℝ)^1673
        have hw : |(-496666489/2500000000 : ℝ)|=(496666489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209883049/400000000 : ℝ)|^2185 ≤ (21536330841499/50000000000000 : ℝ)^1673
        have hw : |(209883049/400000000 : ℝ)|=(209883049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408583087/10000000000 : ℝ)|^2185 ≤ (44812292991389/100000000000000 : ℝ)^1673
        have hw : |(5408583087/10000000000 : ℝ)|=(5408583087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652749983/5000000000 : ℝ)*x 0 + (-953699159/5000000000 : ℝ)*x 1 + (2704291561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652749983/5000000000 : ℝ)^2185 ≤ (10925023405529/25000000000000 : ℝ)^1673 := by
    have hnat : (2652749983 : ℕ)^2185*25000000000000^1673 ≤ 10925023405529^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652749983 5000000000 10925023405529 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953699159/5000000000 : ℝ)^2185 ≤ (11487612989789/100000000000000 : ℝ)^1673 := by
    have hnat : (953699159 : ℕ)^2185*100000000000000^1673 ≤ 11487612989789^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953699159 5000000000 11487612989789 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704291561/5000000000 : ℝ)^2185 ≤ (22406146685063/50000000000000 : ℝ)^1673 := by
    have hnat : (2704291561 : ℕ)^2185*50000000000000^1673 ≤ 22406146685063^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704291561 5000000000 22406146685063 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652749983/5000000000 : ℝ), (-953699159/5000000000 : ℝ), (2704291561/5000000000 : ℝ)] ![(10925023405529/25000000000000 : ℝ), (11487612989789/100000000000000 : ℝ), (22406146685063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652749983/5000000000 : ℝ)|^2185 ≤ (10925023405529/25000000000000 : ℝ)^1673
        have hw : |(2652749983/5000000000 : ℝ)|=(2652749983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953699159/5000000000 : ℝ)|^2185 ≤ (11487612989789/100000000000000 : ℝ)^1673
        have hw : |(-953699159/5000000000 : ℝ)|=(953699159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704291561/5000000000 : ℝ)|^2185 ≤ (22406146685063/50000000000000 : ℝ)^1673
        have hw : |(2704291561/5000000000 : ℝ)|=(2704291561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061100019/2000000000 : ℝ)*x 0 + (2704291527/5000000000 : ℝ)*x 1 + (-476849559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061100019/2000000000 : ℝ)^2185 ≤ (21850047504917/50000000000000 : ℝ)^1673 := by
    have hnat : (1061100019 : ℕ)^2185*50000000000000^1673 ≤ 21850047504917^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061100019 2000000000 21850047504917 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704291527/5000000000 : ℝ)^2185 ≤ (8962458526859/20000000000000 : ℝ)^1673 := by
    have hnat : (2704291527 : ℕ)^2185*20000000000000^1673 ≤ 8962458526859^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704291527 5000000000 8962458526859 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476849559/2500000000 : ℝ)^2185 ≤ (1435951543099/12500000000000 : ℝ)^1673 := by
    have hnat : (476849559 : ℕ)^2185*12500000000000^1673 ≤ 1435951543099^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476849559 2500000000 1435951543099 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061100019/2000000000 : ℝ), (2704291527/5000000000 : ℝ), (-476849559/2500000000 : ℝ)] ![(21850047504917/50000000000000 : ℝ), (8962458526859/20000000000000 : ℝ), (1435951543099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061100019/2000000000 : ℝ)|^2185 ≤ (21850047504917/50000000000000 : ℝ)^1673
        have hw : |(1061100019/2000000000 : ℝ)|=(1061100019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704291527/5000000000 : ℝ)|^2185 ≤ (8962458526859/20000000000000 : ℝ)^1673
        have hw : |(2704291527/5000000000 : ℝ)|=(2704291527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476849559/2500000000 : ℝ)|^2185 ≤ (1435951543099/12500000000000 : ℝ)^1673
        have hw : |(-476849559/2500000000 : ℝ)|=(476849559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s7_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077293463/2500000000 : ℝ)*x 0 + (4485847043/10000000000 : ℝ)*x 1 + (827776883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077293463/2500000000 : ℝ)^2185 ≤ (8326165600027/25000000000000 : ℝ)^1673 := by
    have hnat : (1077293463 : ℕ)^2185*25000000000000^1673 ≤ 8326165600027^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077293463 2500000000 8326165600027 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485847043/10000000000 : ℝ)^2185 ≤ (4387387330523/12500000000000 : ℝ)^1673 := by
    have hnat : (4485847043 : ℕ)^2185*12500000000000^1673 ≤ 4387387330523^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485847043 10000000000 4387387330523 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827776883/2000000000 : ℝ)^2185 ≤ (3949529867777/12500000000000 : ℝ)^1673 := by
    have hnat : (827776883 : ℕ)^2185*12500000000000^1673 ≤ 3949529867777^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827776883 2000000000 3949529867777 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077293463/2500000000 : ℝ), (4485847043/10000000000 : ℝ), (827776883/2000000000 : ℝ)] ![(8326165600027/25000000000000 : ℝ), (4387387330523/12500000000000 : ℝ), (3949529867777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077293463/2500000000 : ℝ)|^2185 ≤ (8326165600027/25000000000000 : ℝ)^1673
        have hw : |(1077293463/2500000000 : ℝ)|=(1077293463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485847043/10000000000 : ℝ)|^2185 ≤ (4387387330523/12500000000000 : ℝ)^1673
        have hw : |(4485847043/10000000000 : ℝ)|=(4485847043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827776883/2000000000 : ℝ)|^2185 ≤ (3949529867777/12500000000000 : ℝ)^1673
        have hw : |(827776883/2000000000 : ℝ)|=(827776883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (11301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1000 : ℝ) ^ (4369/1024 : ℝ) ≤ (227930800663907/2500000000000000000 : ℝ) := by
    have hpowers : (113/1000 : ℝ)^4369 ≤ (227930800663907/2500000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4369*2500000000000000000^1024 ≤ 227930800663907^1024*1000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1000 227930800663907 2500000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1000 : ℝ)) (X := (227930800663907/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (28391597090919117/100000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^4369 ≤ (28391597090919117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14747 : ℕ)^4369*100000000000000000000^1024 ≤ 28391597090919117^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 28391597090919117 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (28391597090919117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250227930800663907/1250000000000000000 : ℝ) ≤ (625026709183957/625000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (1250227930800663907/1250000000000000000 : ℝ)^1024 ≤ (625026709183957/625000000000000 : ℝ)^4369 := by
      have hnat : (1250227930800663907 : ℕ)^1024*625000000000000^4369 ≤ 625026709183957^4369*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250227930800663907 1250000000000000000 625026709183957 625000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625026709183957/625000000000000 : ℝ)) (X := (1250227930800663907/1250000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037508829117475397/100000000000000000000 : ℝ) ≤ (250021975009821/250000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100037508829117475397/100000000000000000000 : ℝ)^1024 ≤ (250021975009821/250000000000000 : ℝ)^4369 := by
      have hnat : (100037508829117475397 : ℕ)^1024*250000000000000^4369 ≤ 250021975009821^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037508829117475397 100000000000000000000 250021975009821 250000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250021975009821/250000000000000 : ℝ)) (X := (100037508829117475397/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028391597090919117/50000000000000000000 : ℝ) ≤ (156270791466287/156250000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50028391597090919117/50000000000000000000 : ℝ)^1024 ≤ (156270791466287/156250000000000 : ℝ)^4369 := by
      have hnat : (50028391597090919117 : ℕ)^1024*156250000000000^4369 ≤ 156270791466287^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028391597090919117 50000000000000000000 156270791466287 156250000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156270791466287/156250000000000 : ℝ)) (X := (50028391597090919117/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(227930800663907/2500000000000000000 : ℝ) ≤ ((2153829106059641479/2154375000000000000 : ℝ)+2*(56456681191/43087500000000 : ℝ)*(113/1000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (2153829106059641479/2154375000000000000 : ℝ)+2*(56456681191/43087500000000 : ℝ)*(113/1000 : ℝ)=(625026709183957/625000000000000 : ℝ) by norm_num, show 1+2*(227930800663907/2500000000000000000 : ℝ)=(1250227930800663907/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28391597090919117/100000000000000000000 : ℝ)+(227930800663907/2500000000000000000 : ℝ) ≤ ((2153829106059641479/2154375000000000000 : ℝ)+(56456681191/43087500000000 : ℝ)*((14747/100000 : ℝ)+(113/1000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (2153829106059641479/2154375000000000000 : ℝ)+(56456681191/43087500000000 : ℝ)*((14747/100000 : ℝ)+(113/1000 : ℝ))=(250021975009821/250000000000000 : ℝ) by norm_num, show 1+(28391597090919117/100000000000000000000 : ℝ)+(227930800663907/2500000000000000000 : ℝ)=(100037508829117475397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28391597090919117/100000000000000000000 : ℝ) ≤ ((2153829106059641479/2154375000000000000 : ℝ)+2*(56456681191/43087500000000 : ℝ)*(14747/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (2153829106059641479/2154375000000000000 : ℝ)+2*(56456681191/43087500000000 : ℝ)*(14747/100000 : ℝ)=(156270791466287/156250000000000 : ℝ) by norm_num, show 1+2*(28391597090919117/100000000000000000000 : ℝ)=(50028391597090919117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2153829106059641479/2154375000000000000 : ℝ)*(X 1 0+X 2 0)+(56456681191/43087500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2153829106059641479/2154375000000000000 : ℝ)) (alpha := (56456681191/43087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2153829106059641479/2154375000000000000 : ℝ)*(X 0 1+X 2 1)+(56456681191/43087500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2153829106059641479/2154375000000000000 : ℝ)) (alpha := (56456681191/43087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2153829106059641479/2154375000000000000 : ℝ)*(X 0 2+X 1 2)+(56456681191/43087500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (2153829106059641479/2154375000000000000 : ℝ)) (alpha := (56456681191/43087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986654399/10000000000 : ℝ)*X 0 0+(5409171661/10000000000 : ℝ)*X 0 1+(5246490731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673856311/5000000000 : ℝ)*X 1 0+(-517372673/2500000000 : ℝ)*X 1 1+(5246490739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668464079/1250000000 : ℝ)*X 2 0+(5246490691/10000000000 : ℝ)*X 2 1+(-1034745371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309149223/10000000000 : ℝ)*X 0 0+(258601243/625000000 : ℝ)*X 0 1+(4487105013/10000000000 : ℝ)*X 0 2+(4309149223/10000000000 : ℝ)*X 1 0+(258601243/625000000 : ℝ)*X 1 1+(4487105013/10000000000 : ℝ)*X 1 2+(4309149223/10000000000 : ℝ)*X 2 0+(258601243/625000000 : ℝ)*X 2 1+(4487105013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-496666489/2500000000 : ℝ)*X 0 0+(209883049/400000000 : ℝ)*X 0 1+(5408583087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652749983/5000000000 : ℝ)*X 1 0+(-953699159/5000000000 : ℝ)*X 1 1+(2704291561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061100019/2000000000 : ℝ)*X 2 0+(2704291527/5000000000 : ℝ)*X 2 1+(-476849559/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077293463/2500000000 : ℝ)*X 0 0+(4485847043/10000000000 : ℝ)*X 0 1+(827776883/2000000000 : ℝ)*X 0 2+(1077293463/2500000000 : ℝ)*X 1 0+(4485847043/10000000000 : ℝ)*X 1 1+(827776883/2000000000 : ℝ)*X 1 2+(1077293463/2500000000 : ℝ)*X 2 0+(4485847043/10000000000 : ℝ)*X 2 1+(827776883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41222096340688615175569043/5984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1228747747/100000000000000 : ℝ)*(base19) + (1072224863/100000000000000 : ℝ)*(base23) + (89850989/100000000000000 : ℝ)*(lower2) + (237965979/100000000000000 : ℝ)*(upper3) + (53944909/100000000000000 : ℝ)*(upper5) + (2252106829604613/50000000000000 : ℝ)*(major0) + (2252106829604613/50000000000000 : ℝ)*(major1) + (2252106829604613/50000000000000 : ℝ)*(major2) + (6147028412118961/100000000000000 : ℝ)*(sp0) + (3073524420019849/50000000000000 : ℝ)*(sp1) + (3073524498281291/50000000000000 : ℝ)*(sp2) + (2861362784280291/100000000000000 : ℝ)*(sp3) + (4331333697/20000000000000 : ℝ)*(sp4) + (3558935279/25000000000000 : ℝ)*(sp7) + (1430688510010703/50000000000000 : ℝ)*(f.failure) + (3073525034393723/50000000000000 : ℝ)*(f.sum) + (9440425957703/2872500000000000000000000000 : ℝ)*base65 + (282761527374291097/11968750000000000000000000000000 : ℝ)*base68 + (82879678501197347/11968750000000000000000000000000 : ℝ)*base70 + (19927180600447347/11968750000000000000000000000000 : ℝ)*base72 + (7965967480331/1436250000000000000000000000 : ℝ)*base74 + (129486722402302653/11968750000000000000000000000000 : ℝ)*base75 + (48224509251822347/11968750000000000000000000000000 : ℝ)*base78 + (94968139328291097/11968750000000000000000000000000 : ℝ)*base80 + (3420568522079/5745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (25849509/5000000000000000000000 : ℝ)*base90 + (25849509/5000000000000000000000 : ℝ)*base92 + (25849509/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (999462163696287165378153/598437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22551351/6250000000000 : ℝ)*(base19) + (548162627/100000000000000 : ℝ)*(base23) + (129757183/100000000000000 : ℝ)*(lower1) + (833469/50000000000000 : ℝ)*(upper2) + (14395487/25000000000000 : ℝ)*(upper3) + (24717889/50000000000000 : ℝ)*(upper5) + (226845805735707/5000000000000 : ℝ)*(major0) + (226845805735707/5000000000000 : ℝ)*(major1) + (226845805735707/5000000000000 : ℝ)*(major2) + (845917591/20000000000000 : ℝ)*(sp2) + (6191680372218303/100000000000000 : ℝ)*(sp4) + (3095840005698343/50000000000000 : ℝ)*(sp5) + (6191675594467721/100000000000000 : ℝ)*(sp6) + (180134487596207/6250000000000 : ℝ)*(sp7) + (180134487596207/6250000000000 : ℝ)*(f.failure) + (6191680372218303/100000000000000 : ℝ)*(f.sum) + (1362348147629/287250000000000000000000000 : ℝ)*base66 + (18597406263661/9350585937500000000000000000 : ℝ)*base68 + (28914205602046179/598437500000000000000000000000 : ℝ)*base70 + (13170992599082983/1196875000000000000000000000000 : ℝ)*base72 + (1369817541551/287250000000000000000000000 : ℝ)*base74 + (4290627337757983/1196875000000000000000000000000 : ℝ)*base76 + (311745023606163/74804687500000000000000000000 : ℝ)*base78 + (1261443927684201/149609375000000000000000000000 : ℝ)*base80 + (12982274619829/574500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10150779/625000000000000000000 : ℝ)*base89 + (10150779/625000000000000000000 : ℝ)*base91 + (10150779/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1410_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_box_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824610263/10000000000 : ℝ)*x 0 + (5387066819/10000000000 : ℝ)*x 1 + (336691681/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824610263/10000000000 : ℝ)^2185 ≤ (10840786403791/100000000000000 : ℝ)^1673 := by
    have hnat : (1824610263 : ℕ)^2185*100000000000000^1673 ≤ 10840786403791^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824610263 10000000000 10840786403791 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387066819/10000000000 : ℝ)^2185 ≤ (44579606370703/100000000000000 : ℝ)^1673 := by
    have hnat : (5387066819 : ℕ)^2185*100000000000000^1673 ≤ 44579606370703^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387066819 10000000000 44579606370703 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336691681/625000000 : ℝ)^2185 ≤ (11144901800727/25000000000000 : ℝ)^1673 := by
    have hnat : (336691681 : ℕ)^2185*25000000000000^1673 ≤ 11144901800727^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336691681 625000000 11144901800727 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824610263/10000000000 : ℝ), (5387066819/10000000000 : ℝ), (336691681/625000000 : ℝ)] ![(10840786403791/100000000000000 : ℝ), (44579606370703/100000000000000 : ℝ), (11144901800727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824610263/10000000000 : ℝ)|^2185 ≤ (10840786403791/100000000000000 : ℝ)^1673
        have hw : |(-1824610263/10000000000 : ℝ)|=(1824610263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387066819/10000000000 : ℝ)|^2185 ≤ (44579606370703/100000000000000 : ℝ)^1673
        have hw : |(5387066819/10000000000 : ℝ)|=(5387066819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336691681/625000000 : ℝ)|^2185 ≤ (11144901800727/25000000000000 : ℝ)^1673
        have hw : |(336691681/625000000 : ℝ)|=(336691681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642958341/5000000000 : ℝ)*x 0 + (-1963497799/10000000000 : ℝ)*x 1 + (5387066291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642958341/5000000000 : ℝ)^2185 ≤ (43489545437947/100000000000000 : ℝ)^1673 := by
    have hnat : (2642958341 : ℕ)^2185*100000000000000^1673 ≤ 43489545437947^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642958341 5000000000 43489545437947 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963497799/10000000000 : ℝ)^2185 ≤ (11930853890639/100000000000000 : ℝ)^1673 := by
    have hnat : (1963497799 : ℕ)^2185*100000000000000^1673 ≤ 11930853890639^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963497799 10000000000 11930853890639 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387066291/10000000000 : ℝ)^2185 ≤ (22289800332079/50000000000000 : ℝ)^1673 := by
    have hnat : (5387066291 : ℕ)^2185*50000000000000^1673 ≤ 22289800332079^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387066291 10000000000 22289800332079 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642958341/5000000000 : ℝ), (-1963497799/10000000000 : ℝ), (5387066291/10000000000 : ℝ)] ![(43489545437947/100000000000000 : ℝ), (11930853890639/100000000000000 : ℝ), (22289800332079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642958341/5000000000 : ℝ)|^2185 ≤ (43489545437947/100000000000000 : ℝ)^1673
        have hw : |(2642958341/5000000000 : ℝ)|=(2642958341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963497799/10000000000 : ℝ)|^2185 ≤ (11930853890639/100000000000000 : ℝ)^1673
        have hw : |(-1963497799/10000000000 : ℝ)|=(1963497799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387066291/10000000000 : ℝ)|^2185 ≤ (22289800332079/50000000000000 : ℝ)^1673
        have hw : |(5387066291/10000000000 : ℝ)|=(5387066291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660739691/1250000000 : ℝ)*x 0 + (5387066433/10000000000 : ℝ)*x 1 + (-1963496459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660739691/1250000000 : ℝ)^2185 ≤ (21744777264251/50000000000000 : ℝ)^1673 := by
    have hnat : (660739691 : ℕ)^2185*50000000000000^1673 ≤ 21744777264251^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660739691 1250000000 21744777264251 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387066433/10000000000 : ℝ)^2185 ≤ (44579602198873/100000000000000 : ℝ)^1673 := by
    have hnat : (5387066433 : ℕ)^2185*100000000000000^1673 ≤ 44579602198873^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387066433 10000000000 44579602198873 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963496459/10000000000 : ℝ)^2185 ≤ (2982710814131/25000000000000 : ℝ)^1673 := by
    have hnat : (1963496459 : ℕ)^2185*25000000000000^1673 ≤ 2982710814131^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963496459 10000000000 2982710814131 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660739691/1250000000 : ℝ), (5387066433/10000000000 : ℝ), (-1963496459/10000000000 : ℝ)] ![(21744777264251/50000000000000 : ℝ), (44579602198873/100000000000000 : ℝ), (2982710814131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660739691/1250000000 : ℝ)|^2185 ≤ (21744777264251/50000000000000 : ℝ)^1673
        have hw : |(660739691/1250000000 : ℝ)|=(660739691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387066433/10000000000 : ℝ)|^2185 ≤ (44579602198873/100000000000000 : ℝ)^1673
        have hw : |(5387066433/10000000000 : ℝ)|=(5387066433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963496459/10000000000 : ℝ)|^2185 ≤ (2982710814131/25000000000000 : ℝ)^1673
        have hw : |(-1963496459/10000000000 : ℝ)|=(1963496459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1113957589/2500000000 : ℝ)*x 0 + (529944269/1250000000 : ℝ)*x 1 + (4239554821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113957589/2500000000 : ℝ)^2185 ≤ (3479267366737/10000000000000 : ℝ)^1673 := by
    have hnat : (1113957589 : ℕ)^2185*10000000000000^1673 ≤ 3479267366737^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113957589 2500000000 3479267366737 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529944269/1250000000 : ℝ)^2185 ≤ (163018299/500000000 : ℝ)^1673 := by
    have hnat : (529944269 : ℕ)^2185*500000000^1673 ≤ 163018299^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529944269 1250000000 163018299 500000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239554821/10000000000 : ℝ)^2185 ≤ (16301833259679/50000000000000 : ℝ)^1673 := by
    have hnat : (4239554821 : ℕ)^2185*50000000000000^1673 ≤ 16301833259679^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239554821 10000000000 16301833259679 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113957589/2500000000 : ℝ), (529944269/1250000000 : ℝ), (4239554821/10000000000 : ℝ)] ![(3479267366737/10000000000000 : ℝ), (163018299/500000000 : ℝ), (16301833259679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113957589/2500000000 : ℝ)|^2185 ≤ (3479267366737/10000000000000 : ℝ)^1673
        have hw : |(1113957589/2500000000 : ℝ)|=(1113957589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529944269/1250000000 : ℝ)|^2185 ≤ (163018299/500000000 : ℝ)^1673
        have hw : |(529944269/1250000000 : ℝ)|=(529944269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239554821/10000000000 : ℝ)|^2185 ≤ (16301833259679/50000000000000 : ℝ)^1673
        have hw : |(4239554821/10000000000 : ℝ)|=(4239554821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430287373/2000000000 : ℝ)*x 0 + (5266232451/10000000000 : ℝ)*x 1 + (1316557989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430287373/2000000000 : ℝ)^2185 ≤ (2688740114087/20000000000000 : ℝ)^1673 := by
    have hnat : (430287373 : ℕ)^2185*20000000000000^1673 ≤ 2688740114087^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430287373 2000000000 2688740114087 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266232451/10000000000 : ℝ)^2185 ≤ (43278152365059/100000000000000 : ℝ)^1673 := by
    have hnat : (5266232451 : ℕ)^2185*100000000000000^1673 ≤ 43278152365059^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266232451 10000000000 43278152365059 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316557989/2500000000 : ℝ)^2185 ≤ (21639073526093/50000000000000 : ℝ)^1673 := by
    have hnat : (1316557989 : ℕ)^2185*50000000000000^1673 ≤ 21639073526093^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316557989 2500000000 21639073526093 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430287373/2000000000 : ℝ), (5266232451/10000000000 : ℝ), (1316557989/2500000000 : ℝ)] ![(2688740114087/20000000000000 : ℝ), (43278152365059/100000000000000 : ℝ), (21639073526093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430287373/2000000000 : ℝ)|^2185 ≤ (2688740114087/20000000000000 : ℝ)^1673
        have hw : |(-430287373/2000000000 : ℝ)|=(430287373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266232451/10000000000 : ℝ)|^2185 ≤ (43278152365059/100000000000000 : ℝ)^1673
        have hw : |(5266232451/10000000000 : ℝ)|=(5266232451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316557989/2500000000 : ℝ)|^2185 ≤ (21639073526093/50000000000000 : ℝ)^1673
        have hw : |(1316557989/2500000000 : ℝ)|=(1316557989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370548297/10000000000 : ℝ)*x 0 + (-2012434279/10000000000 : ℝ)*x 1 + (5266232941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370548297/10000000000 : ℝ)^2185 ≤ (4440116046511/10000000000000 : ℝ)^1673 := by
    have hnat : (5370548297 : ℕ)^2185*10000000000000^1673 ≤ 4440116046511^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370548297 10000000000 4440116046511 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012434279/10000000000 : ℝ)^2185 ≤ (6160340950121/50000000000000 : ℝ)^1673 := by
    have hnat : (2012434279 : ℕ)^2185*50000000000000^1673 ≤ 6160340950121^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012434279 10000000000 6160340950121 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266232941/10000000000 : ℝ)^2185 ≤ (21639078812133/50000000000000 : ℝ)^1673 := by
    have hnat : (5266232941 : ℕ)^2185*50000000000000^1673 ≤ 21639078812133^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266232941 10000000000 21639078812133 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370548297/10000000000 : ℝ), (-2012434279/10000000000 : ℝ), (5266232941/10000000000 : ℝ)] ![(4440116046511/10000000000000 : ℝ), (6160340950121/50000000000000 : ℝ), (21639078812133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370548297/10000000000 : ℝ)|^2185 ≤ (4440116046511/10000000000000 : ℝ)^1673
        have hw : |(5370548297/10000000000 : ℝ)|=(5370548297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2012434279/10000000000 : ℝ)|^2185 ≤ (6160340950121/50000000000000 : ℝ)^1673
        have hw : |(-2012434279/10000000000 : ℝ)|=(2012434279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266232941/10000000000 : ℝ)|^2185 ≤ (21639078812133/50000000000000 : ℝ)^1673
        have hw : |(5266232941/10000000000 : ℝ)|=(5266232941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370548341/10000000000 : ℝ)*x 0 + (5266232359/10000000000 : ℝ)*x 1 + (-2012434999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370548341/10000000000 : ℝ)^2185 ≤ (2775072558763/6250000000000 : ℝ)^1673 := by
    have hnat : (5370548341 : ℕ)^2185*6250000000000^1673 ≤ 2775072558763^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370548341 10000000000 2775072558763 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266232359/10000000000 : ℝ)^2185 ≤ (2704884461101/6250000000000 : ℝ)^1673 := by
    have hnat : (5266232359 : ℕ)^2185*6250000000000^1673 ≤ 2704884461101^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266232359 10000000000 2704884461101 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012434999/10000000000 : ℝ)^2185 ≤ (6160343828653/50000000000000 : ℝ)^1673 := by
    have hnat : (2012434999 : ℕ)^2185*50000000000000^1673 ≤ 6160343828653^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012434999 10000000000 6160343828653 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370548341/10000000000 : ℝ), (5266232359/10000000000 : ℝ), (-2012434999/10000000000 : ℝ)] ![(2775072558763/6250000000000 : ℝ), (2704884461101/6250000000000 : ℝ), (6160343828653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370548341/10000000000 : ℝ)|^2185 ≤ (2775072558763/6250000000000 : ℝ)^1673
        have hw : |(5370548341/10000000000 : ℝ)|=(5370548341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266232359/10000000000 : ℝ)|^2185 ≤ (2704884461101/6250000000000 : ℝ)^1673
        have hw : |(5266232359/10000000000 : ℝ)|=(5266232359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2012434999/10000000000 : ℝ)|^2185 ≤ (6160343828653/50000000000000 : ℝ)^1673
        have hw : |(-2012434999/10000000000 : ℝ)|=(2012434999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (130045137/312500000 : ℝ)*x 0 + (4386695861/10000000000 : ℝ)*x 1 + (4386696177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130045137/312500000 : ℝ)^2185 ≤ (31821355641881/100000000000000 : ℝ)^1673 := by
    have hnat : (130045137 : ℕ)^2185*100000000000000^1673 ≤ 31821355641881^1673*312500000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130045137 312500000 31821355641881 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4386695861/10000000000 : ℝ)^2185 ≤ (34089320567211/100000000000000 : ℝ)^1673 := by
    have hnat : (4386695861 : ℕ)^2185*100000000000000^1673 ≤ 34089320567211^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386695861 10000000000 34089320567211 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386696177/10000000000 : ℝ)^2185 ≤ (34089323774391/100000000000000 : ℝ)^1673 := by
    have hnat : (4386696177 : ℕ)^2185*100000000000000^1673 ≤ 34089323774391^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386696177 10000000000 34089323774391 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130045137/312500000 : ℝ), (4386695861/10000000000 : ℝ), (4386696177/10000000000 : ℝ)] ![(31821355641881/100000000000000 : ℝ), (34089320567211/100000000000000 : ℝ), (34089323774391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130045137/312500000 : ℝ)|^2185 ≤ (31821355641881/100000000000000 : ℝ)^1673
        have hw : |(130045137/312500000 : ℝ)|=(130045137/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4386695861/10000000000 : ℝ)|^2185 ≤ (34089320567211/100000000000000 : ℝ)^1673
        have hw : |(4386695861/10000000000 : ℝ)|=(4386695861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386696177/10000000000 : ℝ)|^2185 ≤ (34089323774391/100000000000000 : ℝ)^1673
        have hw : |(4386696177/10000000000 : ℝ)|=(4386696177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_8 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-416527979/2000000000 : ℝ)*x 0 + (2591368547/5000000000 : ℝ)*x 1 + (5401051809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416527979/2000000000 : ℝ)^2185 ≤ (1610626665637/12500000000000 : ℝ)^1673 := by
    have hnat : (416527979 : ℕ)^2185*12500000000000^1673 ≤ 1610626665637^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416527979 2000000000 1610626665637 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591368547/5000000000 : ℝ)^2185 ≤ (42384172583603/100000000000000 : ℝ)^1673 := by
    have hnat : (2591368547 : ℕ)^2185*100000000000000^1673 ≤ 42384172583603^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591368547 5000000000 42384172583603 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401051809/10000000000 : ℝ)^2185 ≤ (5591351758919/12500000000000 : ℝ)^1673 := by
    have hnat : (5401051809 : ℕ)^2185*12500000000000^1673 ≤ 5591351758919^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051809 10000000000 5591351758919 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416527979/2000000000 : ℝ), (2591368547/5000000000 : ℝ), (5401051809/10000000000 : ℝ)] ![(1610626665637/12500000000000 : ℝ), (42384172583603/100000000000000 : ℝ), (5591351758919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416527979/2000000000 : ℝ)|^2185 ≤ (1610626665637/12500000000000 : ℝ)^1673
        have hw : |(-416527979/2000000000 : ℝ)|=(416527979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591368547/5000000000 : ℝ)|^2185 ≤ (42384172583603/100000000000000 : ℝ)^1673
        have hw : |(2591368547/5000000000 : ℝ)|=(2591368547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401051809/10000000000 : ℝ)|^2185 ≤ (5591351758919/12500000000000 : ℝ)^1673
        have hw : |(5401051809/10000000000 : ℝ)|=(5401051809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_9 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1319029363/2500000000 : ℝ)*x 0 + (-1957705389/10000000000 : ℝ)*x 1 + (5401051809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319029363/2500000000 : ℝ)^2185 ≤ (2711517455499/6250000000000 : ℝ)^1673 := by
    have hnat : (1319029363 : ℕ)^2185*6250000000000^1673 ≤ 2711517455499^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319029363 2500000000 2711517455499 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957705389/10000000000 : ℝ)^2185 ≤ (11884906624129/100000000000000 : ℝ)^1673 := by
    have hnat : (1957705389 : ℕ)^2185*100000000000000^1673 ≤ 11884906624129^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957705389 10000000000 11884906624129 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401051809/10000000000 : ℝ)^2185 ≤ (5591351758919/12500000000000 : ℝ)^1673 := by
    have hnat : (5401051809 : ℕ)^2185*12500000000000^1673 ≤ 5591351758919^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051809 10000000000 5591351758919 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319029363/2500000000 : ℝ), (-1957705389/10000000000 : ℝ), (5401051809/10000000000 : ℝ)] ![(2711517455499/6250000000000 : ℝ), (11884906624129/100000000000000 : ℝ), (5591351758919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319029363/2500000000 : ℝ)|^2185 ≤ (2711517455499/6250000000000 : ℝ)^1673
        have hw : |(1319029363/2500000000 : ℝ)|=(1319029363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957705389/10000000000 : ℝ)|^2185 ≤ (11884906624129/100000000000000 : ℝ)^1673
        have hw : |(-1957705389/10000000000 : ℝ)|=(1957705389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401051809/10000000000 : ℝ)|^2185 ≤ (5591351758919/12500000000000 : ℝ)^1673
        have hw : |(5401051809/10000000000 : ℝ)|=(5401051809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_10 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1055223463/2000000000 : ℝ)*x 0 + (5401051713/10000000000 : ℝ)*x 1 + (-978852853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055223463/2000000000 : ℝ)^2185 ≤ (43384277816709/100000000000000 : ℝ)^1673 := by
    have hnat : (1055223463 : ℕ)^2185*100000000000000^1673 ≤ 43384277816709^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055223463 2000000000 43384277816709 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401051713/10000000000 : ℝ)^2185 ≤ (1789232521319/4000000000000 : ℝ)^1673 := by
    have hnat : (5401051713 : ℕ)^2185*4000000000000^1673 ≤ 1789232521319^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051713 10000000000 1789232521319 4000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978852853/5000000000 : ℝ)^2185 ≤ (5942454568769/50000000000000 : ℝ)^1673 := by
    have hnat : (978852853 : ℕ)^2185*50000000000000^1673 ≤ 5942454568769^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978852853 5000000000 5942454568769 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055223463/2000000000 : ℝ), (5401051713/10000000000 : ℝ), (-978852853/5000000000 : ℝ)] ![(43384277816709/100000000000000 : ℝ), (1789232521319/4000000000000 : ℝ), (5942454568769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055223463/2000000000 : ℝ)|^2185 ≤ (43384277816709/100000000000000 : ℝ)^1673
        have hw : |(1055223463/2000000000 : ℝ)|=(1055223463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401051713/10000000000 : ℝ)|^2185 ≤ (1789232521319/4000000000000 : ℝ)^1673
        have hw : |(5401051713/10000000000 : ℝ)|=(5401051713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978852853/5000000000 : ℝ)|^2185 ≤ (5942454568769/50000000000000 : ℝ)^1673
        have hw : |(-978852853/5000000000 : ℝ)|=(978852853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_11 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4489344499/10000000000 : ℝ)*x 0 + (4222510347/10000000000 : ℝ)*x 1 + (4222510173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489344499/10000000000 : ℝ)^2185 ≤ (1097963852979/3125000000000 : ℝ)^1673 := by
    have hnat : (4489344499 : ℕ)^2185*3125000000000^1673 ≤ 1097963852979^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489344499 10000000000 1097963852979 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222510347/10000000000 : ℝ)^2185 ≤ (1621628960687/5000000000000 : ℝ)^1673 := by
    have hnat : (4222510347 : ℕ)^2185*5000000000000^1673 ≤ 1621628960687^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222510347 10000000000 1621628960687 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222510173/10000000000 : ℝ)^2185 ≤ (32432577468257/100000000000000 : ℝ)^1673 := by
    have hnat : (4222510173 : ℕ)^2185*100000000000000^1673 ≤ 32432577468257^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222510173 10000000000 32432577468257 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489344499/10000000000 : ℝ), (4222510347/10000000000 : ℝ), (4222510173/10000000000 : ℝ)] ![(1097963852979/3125000000000 : ℝ), (1621628960687/5000000000000 : ℝ), (32432577468257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489344499/10000000000 : ℝ)|^2185 ≤ (1097963852979/3125000000000 : ℝ)^1673
        have hw : |(4489344499/10000000000 : ℝ)|=(4489344499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222510347/10000000000 : ℝ)|^2185 ≤ (1621628960687/5000000000000 : ℝ)^1673
        have hw : |(4222510347/10000000000 : ℝ)|=(4222510347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222510173/10000000000 : ℝ)|^2185 ≤ (32432577468257/100000000000000 : ℝ)^1673
        have hw : |(4222510173/10000000000 : ℝ)|=(4222510173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_12 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-473405083/2500000000 : ℝ)*x 0 + (1093700093/2000000000 : ℝ)*x 1 + (2627558329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473405083/2500000000 : ℝ)^2185 ≤ (455174313907/4000000000000 : ℝ)^1673 := by
    have hnat : (473405083 : ℕ)^2185*4000000000000^1673 ≤ 455174313907^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473405083 2500000000 455174313907 4000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093700093/2000000000 : ℝ)^2185 ≤ (22730878932237/50000000000000 : ℝ)^1673 := by
    have hnat : (1093700093 : ℕ)^2185*50000000000000^1673 ≤ 22730878932237^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093700093 2000000000 22730878932237 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627558329/5000000000 : ℝ)^2185 ≤ (1348715133503/3125000000000 : ℝ)^1673 := by
    have hnat : (2627558329 : ℕ)^2185*3125000000000^1673 ≤ 1348715133503^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627558329 5000000000 1348715133503 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473405083/2500000000 : ℝ), (1093700093/2000000000 : ℝ), (2627558329/5000000000 : ℝ)] ![(455174313907/4000000000000 : ℝ), (22730878932237/50000000000000 : ℝ), (1348715133503/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473405083/2500000000 : ℝ)|^2185 ≤ (455174313907/4000000000000 : ℝ)^1673
        have hw : |(-473405083/2500000000 : ℝ)|=(473405083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093700093/2000000000 : ℝ)|^2185 ≤ (22730878932237/50000000000000 : ℝ)^1673
        have hw : |(1093700093/2000000000 : ℝ)|=(1093700093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627558329/5000000000 : ℝ)|^2185 ≤ (1348715133503/3125000000000 : ℝ)^1673
        have hw : |(2627558329/5000000000 : ℝ)|=(2627558329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_13 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (672291589/1250000000 : ℝ)*x 0 + (-2016836253/10000000000 : ℝ)*x 1 + (5255115849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672291589/1250000000 : ℝ)^2185 ≤ (22242616433677/50000000000000 : ℝ)^1673 := by
    have hnat : (672291589 : ℕ)^2185*50000000000000^1673 ≤ 22242616433677^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672291589 1250000000 22242616433677 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016836253/10000000000 : ℝ)^2185 ≤ (193060804927/1562500000000 : ℝ)^1673 := by
    have hnat : (2016836253 : ℕ)^2185*1562500000000^1673 ≤ 193060804927^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016836253 10000000000 193060804927 1562500000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255115849/10000000000 : ℝ)^2185 ≤ (43158875594651/100000000000000 : ℝ)^1673 := by
    have hnat : (5255115849 : ℕ)^2185*100000000000000^1673 ≤ 43158875594651^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255115849 10000000000 43158875594651 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672291589/1250000000 : ℝ), (-2016836253/10000000000 : ℝ), (5255115849/10000000000 : ℝ)] ![(22242616433677/50000000000000 : ℝ), (193060804927/1562500000000 : ℝ), (43158875594651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672291589/1250000000 : ℝ)|^2185 ≤ (22242616433677/50000000000000 : ℝ)^1673
        have hw : |(672291589/1250000000 : ℝ)|=(672291589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016836253/10000000000 : ℝ)|^2185 ≤ (193060804927/1562500000000 : ℝ)^1673
        have hw : |(-2016836253/10000000000 : ℝ)|=(2016836253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255115849/10000000000 : ℝ)|^2185 ≤ (43158875594651/100000000000000 : ℝ)^1673
        have hw : |(5255115849/10000000000 : ℝ)|=(5255115849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_14 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (336145767/625000000 : ℝ)*x 0 + (164222379/312500000 : ℝ)*x 1 + (-2016836473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336145767/625000000 : ℝ)^2185 ≤ (2224261405713/5000000000000 : ℝ)^1673 := by
    have hnat : (336145767 : ℕ)^2185*5000000000000^1673 ≤ 2224261405713^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336145767 625000000 2224261405713 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164222379/312500000 : ℝ)^2185 ≤ (43158878587243/100000000000000 : ℝ)^1673 := by
    have hnat : (164222379 : ℕ)^2185*100000000000000^1673 ≤ 43158878587243^1673*312500000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164222379 312500000 43158878587243 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016836473/10000000000 : ℝ)^2185 ≤ (1544486659451/12500000000000 : ℝ)^1673 := by
    have hnat : (2016836473 : ℕ)^2185*12500000000000^1673 ≤ 1544486659451^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016836473 10000000000 1544486659451 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336145767/625000000 : ℝ), (164222379/312500000 : ℝ), (-2016836473/10000000000 : ℝ)] ![(2224261405713/5000000000000 : ℝ), (43158878587243/100000000000000 : ℝ), (1544486659451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336145767/625000000 : ℝ)|^2185 ≤ (2224261405713/5000000000000 : ℝ)^1673
        have hw : |(336145767/625000000 : ℝ)|=(336145767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164222379/312500000 : ℝ)|^2185 ≤ (43158878587243/100000000000000 : ℝ)^1673
        have hw : |(164222379/312500000 : ℝ)|=(164222379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016836473/10000000000 : ℝ)|^2185 ≤ (1544486659451/12500000000000 : ℝ)^1673
        have hw : |(-2016836473/10000000000 : ℝ)|=(2016836473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_box_15 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4133915029/10000000000 : ℝ)*x 0 + (275013797/625000000 : ℝ)*x 1 + (4400219873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133915029/10000000000 : ℝ)^2185 ≤ (31546701850677/100000000000000 : ℝ)^1673 := by
    have hnat : (4133915029 : ℕ)^2185*100000000000000^1673 ≤ 31546701850677^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133915029 10000000000 31546701850677 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275013797/625000000 : ℝ)^2185 ≤ (1069582922839/3125000000000 : ℝ)^1673 := by
    have hnat : (275013797 : ℕ)^2185*3125000000000^1673 ≤ 1069582922839^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275013797 625000000 1069582922839 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4400219873/10000000000 : ℝ)^2185 ≤ (85566611503/250000000000 : ℝ)^1673 := by
    have hnat : (4400219873 : ℕ)^2185*250000000000^1673 ≤ 85566611503^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400219873 10000000000 85566611503 250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133915029/10000000000 : ℝ), (275013797/625000000 : ℝ), (4400219873/10000000000 : ℝ)] ![(31546701850677/100000000000000 : ℝ), (1069582922839/3125000000000 : ℝ), (85566611503/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133915029/10000000000 : ℝ)|^2185 ≤ (31546701850677/100000000000000 : ℝ)^1673
        have hw : |(4133915029/10000000000 : ℝ)|=(4133915029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275013797/625000000 : ℝ)|^2185 ≤ (1069582922839/3125000000000 : ℝ)^1673
        have hw : |(275013797/625000000 : ℝ)|=(275013797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4400219873/10000000000 : ℝ)|^2185 ≤ (85566611503/250000000000 : ℝ)^1673
        have hw : |(4400219873/10000000000 : ℝ)|=(4400219873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7861/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2363/4000 : ℝ) ∧ (80343/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84613/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11301/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (9120674966319961/100000000000000000000 : ℝ) := by
    have hpowers : (11301/100000 : ℝ)^4369 ≤ (9120674966319961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11301 : ℕ)^4369*100000000000000000000^1024 ≤ 9120674966319961^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11301 100000 9120674966319961 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11301/100000 : ℝ)) (X := (9120674966319961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (4369/1024 : ℝ) ≤ (14191691872344801/50000000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^4369 ≤ (14191691872344801/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7373 : ℕ)^4369*50000000000000000000^1024 ≤ 14191691872344801^1024*50000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 14191691872344801 50000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (14191691872344801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009120674966319961/50000000000000000000 : ℝ) ≤ (2500106877077761/2500000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50009120674966319961/50000000000000000000 : ℝ)^1024 ≤ (2500106877077761/2500000000000000 : ℝ)^4369 := by
      have hnat : (50009120674966319961 : ℕ)^1024*2500000000000000^4369 ≤ 2500106877077761^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009120674966319961 50000000000000000000 2500106877077761 2500000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500106877077761/2500000000000000 : ℝ)) (X := (50009120674966319961/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037504058711009563/100000000000000000000 : ℝ) ≤ (2500219722154207/2500000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100037504058711009563/100000000000000000000 : ℝ)^1024 ≤ (2500219722154207/2500000000000000 : ℝ)^4369 := by
      have hnat : (100037504058711009563 : ℕ)^1024*2500000000000000^4369 ≤ 2500219722154207^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037504058711009563 100000000000000000000 2500219722154207 2500000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500219722154207/2500000000000000 : ℝ)) (X := (100037504058711009563/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014191691872344801/25000000000000000000 : ℝ) ≤ (2500332567230653/2500000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (25014191691872344801/25000000000000000000 : ℝ)^1024 ≤ (2500332567230653/2500000000000000 : ℝ)^4369 := by
      have hnat : (25014191691872344801 : ℕ)^1024*2500000000000000^4369 ≤ 2500332567230653^4369*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014191691872344801 25000000000000000000 2500332567230653 2500000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500332567230653/2500000000000000 : ℝ)) (X := (25014191691872344801/25000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9120674966319961/100000000000000000000 : ℝ) ≤ ((8610317667115054153/8612500000000000000 : ℝ)+2*(56422538223/43062500000000 : ℝ)*(11301/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (8610317667115054153/8612500000000000000 : ℝ)+2*(56422538223/43062500000000 : ℝ)*(11301/100000 : ℝ)=(2500106877077761/2500000000000000 : ℝ) by norm_num, show 1+2*(9120674966319961/100000000000000000000 : ℝ)=(50009120674966319961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14191691872344801/50000000000000000000 : ℝ)+(9120674966319961/100000000000000000000 : ℝ) ≤ ((8610317667115054153/8612500000000000000 : ℝ)+(56422538223/43062500000000 : ℝ)*((7373/50000 : ℝ)+(11301/100000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (8610317667115054153/8612500000000000000 : ℝ)+(56422538223/43062500000000 : ℝ)*((7373/50000 : ℝ)+(11301/100000 : ℝ))=(2500219722154207/2500000000000000 : ℝ) by norm_num, show 1+(14191691872344801/50000000000000000000 : ℝ)+(9120674966319961/100000000000000000000 : ℝ)=(100037504058711009563/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14191691872344801/50000000000000000000 : ℝ) ≤ ((8610317667115054153/8612500000000000000 : ℝ)+2*(56422538223/43062500000000 : ℝ)*(7373/50000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (8610317667115054153/8612500000000000000 : ℝ)+2*(56422538223/43062500000000 : ℝ)*(7373/50000 : ℝ)=(2500332567230653/2500000000000000 : ℝ) by norm_num, show 1+2*(14191691872344801/50000000000000000000 : ℝ)=(25014191691872344801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8610317667115054153/8612500000000000000 : ℝ)*(X 1 0+X 2 0)+(56422538223/43062500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (8610317667115054153/8612500000000000000 : ℝ)) (alpha := (56422538223/43062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8610317667115054153/8612500000000000000 : ℝ)*(X 0 1+X 2 1)+(56422538223/43062500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (8610317667115054153/8612500000000000000 : ℝ)) (alpha := (56422538223/43062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8610317667115054153/8612500000000000000 : ℝ)*(X 0 2+X 1 2)+(56422538223/43062500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (8610317667115054153/8612500000000000000 : ℝ)) (alpha := (56422538223/43062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824610263/10000000000 : ℝ)*X 0 0+(5387066819/10000000000 : ℝ)*X 0 1+(336691681/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642958341/5000000000 : ℝ)*X 1 0+(-1963497799/10000000000 : ℝ)*X 1 1+(5387066291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660739691/1250000000 : ℝ)*X 2 0+(5387066433/10000000000 : ℝ)*X 2 1+(-1963496459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1113957589/2500000000 : ℝ)*X 0 0+(529944269/1250000000 : ℝ)*X 0 1+(4239554821/10000000000 : ℝ)*X 0 2+(1113957589/2500000000 : ℝ)*X 1 0+(529944269/1250000000 : ℝ)*X 1 1+(4239554821/10000000000 : ℝ)*X 1 2+(1113957589/2500000000 : ℝ)*X 2 0+(529944269/1250000000 : ℝ)*X 2 1+(4239554821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430287373/2000000000 : ℝ)*X 0 0+(5266232451/10000000000 : ℝ)*X 0 1+(1316557989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370548297/10000000000 : ℝ)*X 1 0+(-2012434279/10000000000 : ℝ)*X 1 1+(5266232941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370548341/10000000000 : ℝ)*X 2 0+(5266232359/10000000000 : ℝ)*X 2 1+(-2012434999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((130045137/312500000 : ℝ)*X 0 0+(4386695861/10000000000 : ℝ)*X 0 1+(4386696177/10000000000 : ℝ)*X 0 2+(130045137/312500000 : ℝ)*X 1 0+(4386695861/10000000000 : ℝ)*X 1 1+(4386696177/10000000000 : ℝ)*X 1 2+(130045137/312500000 : ℝ)*X 2 0+(4386695861/10000000000 : ℝ)*X 2 1+(4386696177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-416527979/2000000000 : ℝ)*X 0 0+(2591368547/5000000000 : ℝ)*X 0 1+(5401051809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1319029363/2500000000 : ℝ)*X 1 0+(-1957705389/10000000000 : ℝ)*X 1 1+(5401051809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055223463/2000000000 : ℝ)*X 2 0+(5401051713/10000000000 : ℝ)*X 2 1+(-978852853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489344499/10000000000 : ℝ)*X 0 0+(4222510347/10000000000 : ℝ)*X 0 1+(4222510173/10000000000 : ℝ)*X 0 2+(4489344499/10000000000 : ℝ)*X 1 0+(4222510347/10000000000 : ℝ)*X 1 1+(4222510173/10000000000 : ℝ)*X 1 2+(4489344499/10000000000 : ℝ)*X 2 0+(4222510347/10000000000 : ℝ)*X 2 1+(4222510173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-473405083/2500000000 : ℝ)*X 0 0+(1093700093/2000000000 : ℝ)*X 0 1+(2627558329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672291589/1250000000 : ℝ)*X 1 0+(-2016836253/10000000000 : ℝ)*X 1 1+(5255115849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336145767/625000000 : ℝ)*X 2 0+(164222379/312500000 : ℝ)*X 2 1+(-2016836473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4133915029/10000000000 : ℝ)*X 0 0+(275013797/625000000 : ℝ)*X 0 1+(4400219873/10000000000 : ℝ)*X 0 2+(4133915029/10000000000 : ℝ)*X 1 0+(275013797/625000000 : ℝ)*X 1 1+(4400219873/10000000000 : ℝ)*X 1 2+(4133915029/10000000000 : ℝ)*X 2 0+(275013797/625000000 : ℝ)*X 2 1+(4400219873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7861/12500 : ℝ) ≤ (-13540062202168366736256889405341/21531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22237597/50000000000000 : ℝ)*(upper3) + (43586451/20000000000000 : ℝ)*(lower4) + (57823939/100000000000000 : ℝ)*(lower5) + (149804878851699/5000000000000 : ℝ)*(major0) + (149804878851699/5000000000000 : ℝ)*(major1) + (149804878851699/5000000000000 : ℝ)*(major2) + (4394571767/50000000000000 : ℝ)*(sp3) + (2054917905968169/50000000000000 : ℝ)*(sp4) + (2054756821979017/50000000000000 : ℝ)*(sp5) + (102745420814539/2500000000000 : ℝ)*(sp6) + (1903312279815691/100000000000000 : ℝ)*(sp7) + (2341061/1562500000000 : ℝ)*(sp8) + (2518107861/781250000000 : ℝ)*(sp13) + (9564591341/50000000000000 : ℝ)*(sp14) + (76132842758369/4000000000000 : ℝ)*(f.failure) + (2054917980882121/50000000000000 : ℝ)*(f.sum) + (5739807574977/1722500000000000000000000000 : ℝ)*base65 + (16889852626643447/43062500000000000000000000000000 : ℝ)*base67 + (209684857174893447/43062500000000000000000000000000 : ℝ)*base69 + (32650378432830947/43062500000000000000000000000000 : ℝ)*base71 + (11411111287059/3445000000000000000000000000 : ℝ)*base73 + (145405759608768447/43062500000000000000000000000000 : ℝ)*base75 + (182148010006544053/43062500000000000000000000000000 : ℝ)*base78 + (82860980264481553/43062500000000000000000000000000 : ℝ)*base80 + (10249768418789/3445000000000000000000000000 : ℝ)*base81 + (1164693/400000000000000000000 : ℝ)*base89 + (1164693/400000000000000000000 : ℝ)*base91 + (1164693/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2363/4000 : ℝ) ≤ (1272015606938789300456975049/2153125000000000000000000000 : ℝ) := by norm_num
    linear_combination (218828691/50000000000000 : ℝ)*(lower1) + (2835217/10000000000000 : ℝ)*(lower3) + (34245041/5000000000000 : ℝ)*(upper4) + (13017389/50000000000000 : ℝ)*(upper5) + (23961294285107/781250000000 : ℝ)*(major0) + (23961294285107/781250000000 : ℝ)*(major1) + (23961294285107/781250000000 : ℝ)*(major2) + (2083003378820943/50000000000000 : ℝ)*(sp0) + (208276693830411/5000000000000 : ℝ)*(sp1) + (2082936579071749/50000000000000 : ℝ)*(sp2) + (608871734217/31250000000 : ℝ)*(sp3) + (496108387/20000000000000 : ℝ)*(sp7) + (236440516833/50000000000000 : ℝ)*(sp9) + (33399874597/25000000000000 : ℝ)*(sp10) + (389678406007267/20000000000000 : ℝ)*(f.failure) + (2083003378820943/50000000000000 : ℝ)*(f.sum) + (18782442928143/8612500000000000000000000000 : ℝ)*base66 + (520391502968404343/53828125000000000000000000000000 : ℝ)*base67 + (161806252054876907/53828125000000000000000000000000 : ℝ)*base70 + (4366157203431879/6728515625000000000000000000000 : ℝ)*base72 + (80111619314939/17225000000000000000000000000 : ℝ)*base73 + (152176828856595657/53828125000000000000000000000000 : ℝ)*base76 + (158130081151964367/13457031250000000000000000000000 : ℝ)*base77 + (285380027678091843/53828125000000000000000000000000 : ℝ)*base79 + (188161957818961/17225000000000000000000000000 : ℝ)*base82 + (9030401/2000000000000000000000 : ℝ)*base90 + (9030401/2000000000000000000000 : ℝ)*base92 + (9030401/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80343/100000 : ℝ) ≤ (172994211447146516440578049344303/215312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84123423/100000000000000 : ℝ)*(upper1) + (14530029/10000000000000 : ℝ)*(upper2) + (3099917/6250000000000 : ℝ)*(lower5) + (1687995320218339/50000000000000 : ℝ)*(major0) + (1687995320218339/50000000000000 : ℝ)*(major1) + (1687995320218339/50000000000000 : ℝ)*(major2) + (11659567467/12500000000000 : ℝ)*(sp1) + (903756041/10000000000000 : ℝ)*(sp2) + (5927103773/25000000000000 : ℝ)*(sp3) + (1718168689/50000000000000 : ℝ)*(sp4) + (4580541475885443/100000000000000 : ℝ)*(sp8) + (916090327136617/20000000000000 : ℝ)*(sp9) + (4580535874662411/100000000000000 : ℝ)*(sp10) + (2144630779411491/100000000000000 : ℝ)*(sp11) + (2144654487826583/100000000000000 : ℝ)*(f.failure) + (229027245611141/5000000000000 : ℝ)*(f.sum) + (75306794462351/8612500000000000000000000000 : ℝ)*base65 + (3201573616917513133/430625000000000000000000000000000 : ℝ)*base68 + (3652648459455638133/430625000000000000000000000000000 : ℝ)*base70 + (6311422766435013133/430625000000000000000000000000000 : ℝ)*base72 + (1336285319511/538281250000000000000000000 : ℝ)*base73 + (5678662513301888133/430625000000000000000000000000000 : ℝ)*base76 + (5263556071308138133/430625000000000000000000000000000 : ℝ)*base78 + (5186927742615638133/430625000000000000000000000000000 : ℝ)*base80 + (49431031120777/17225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (38198851/10000000000000000000000 : ℝ)*base89 + (38198851/10000000000000000000000 : ℝ)*base91 + (38198851/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84613/100000 : ℝ) ≤ (-3503410923467546845750123645443/4140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107054361/100000000000000 : ℝ)*(lower0) + (161319727/100000000000000 : ℝ)*(upper1) + (35802897/100000000000000 : ℝ)*(upper3) + (187663109/100000000000000 : ℝ)*(lower4) + (53332097293197/1562500000000 : ℝ)*(major0) + (53332097293197/1562500000000 : ℝ)*(major1) + (53332097293197/1562500000000 : ℝ)*(major2) + (114063881617/50000000000000 : ℝ)*(sp5) + (51081605629/25000000000000 : ℝ)*(sp6) + (723984111/1250000000000 : ℝ)*(sp7) + (937277041844083/20000000000000 : ℝ)*(sp12) + (4686157081457181/100000000000000 : ℝ)*(sp13) + (2343090441398949/50000000000000 : ℝ)*(sp14) + (2168268885215371/100000000000000 : ℝ)*(sp15) + (2168326803944251/100000000000000 : ℝ)*(f.failure) + (937277041844083/20000000000000 : ℝ)*(f.sum) + (66365234957397/17225000000000000000000000000 : ℝ)*base65 + (285577345733866689/53828125000000000000000000000000 : ℝ)*base67 + (250351349615664561/53828125000000000000000000000000 : ℝ)*base70 + (579306636594960439/53828125000000000000000000000000 : ℝ)*base71 + (51286113503247/17225000000000000000000000000 : ℝ)*base73 + (54318478611621343/26914062500000000000000000000000 : ℝ)*base76 + (565392451584179189/53828125000000000000000000000000 : ℝ)*base77 + (87542391500356383/6728515625000000000000000000000 : ℝ)*base79 + (155161106383453/17225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (96068553/10000000000000000000000 : ℝ)*base90 + (96068553/10000000000000000000000 : ℝ)*base92 + (96068553/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1410_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(2363/4000 : ℝ) else (80343/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84613/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1410_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1410_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(2363/4000 : ℝ) else (80343/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84613/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1410_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1410_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1410_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7861/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(2363/4000 : ℝ) else (80343/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84613/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
