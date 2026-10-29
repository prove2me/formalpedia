-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1524_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:03:27.588706+00:00
-- url     : https://prove2.me/submissions/59419ad5-a214-48e7-818b-bc8836ef7cfd

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
theorem support_rectangle_w1524_s6_0 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167216091/312500000 : ℝ)*x 0 + (652277667/1250000000 : ℝ)*x 1 + (-1959728971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167216091/312500000 : ℝ)^4545 ≤ (44611593074597/100000000000000 : ℝ)^3521 := by
    have hnat : (167216091 : ℕ)^4545*100000000000000^3521 ≤ 44611593074597^3521*312500000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167216091 312500000 44611593074597 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652277667/1250000000 : ℝ)^4545 ≤ (1079718567017/2500000000000 : ℝ)^3521 := by
    have hnat : (652277667 : ℕ)^4545*2500000000000^3521 ≤ 1079718567017^3521*1250000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652277667 1250000000 1079718567017 2500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959728971/10000000000 : ℝ)^4545 ≤ (2439932847563/20000000000000 : ℝ)^3521 := by
    have hnat : (1959728971 : ℕ)^4545*20000000000000^3521 ≤ 2439932847563^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959728971 10000000000 2439932847563 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167216091/312500000 : ℝ), (652277667/1250000000 : ℝ), (-1959728971/10000000000 : ℝ)] ![(44611593074597/100000000000000 : ℝ), (1079718567017/2500000000000 : ℝ), (2439932847563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167216091/312500000 : ℝ)|^4545 ≤ (44611593074597/100000000000000 : ℝ)^3521
        have hw : |(167216091/312500000 : ℝ)|=(167216091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652277667/1250000000 : ℝ)|^4545 ≤ (1079718567017/2500000000000 : ℝ)^3521
        have hw : |(652277667/1250000000 : ℝ)|=(652277667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959728971/10000000000 : ℝ)|^4545 ≤ (2439932847563/20000000000000 : ℝ)^3521
        have hw : |(-1959728971/10000000000 : ℝ)|=(1959728971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s6_1 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4626157/25000000 : ℝ)*x 0 + (5219322487/10000000000 : ℝ)*x 1 + (2715282977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4626157/25000000 : ℝ)^4545 ≤ (2832214233179/25000000000000 : ℝ)^3521 := by
    have hnat : (4626157 : ℕ)^4545*25000000000000^3521 ≤ 2832214233179^3521*25000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4626157 25000000 2832214233179 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219322487/10000000000 : ℝ)^4545 ≤ (8640101450527/20000000000000 : ℝ)^3521 := by
    have hnat : (5219322487 : ℕ)^4545*20000000000000^3521 ≤ 8640101450527^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219322487 10000000000 8640101450527 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715282977/5000000000 : ℝ)^4545 ≤ (5683829475603/12500000000000 : ℝ)^3521 := by
    have hnat : (2715282977 : ℕ)^4545*12500000000000^3521 ≤ 5683829475603^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715282977 5000000000 5683829475603 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4626157/25000000 : ℝ), (5219322487/10000000000 : ℝ), (2715282977/5000000000 : ℝ)] ![(2832214233179/25000000000000 : ℝ), (8640101450527/20000000000000 : ℝ), (5683829475603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4626157/25000000 : ℝ)|^4545 ≤ (2832214233179/25000000000000 : ℝ)^3521
        have hw : |(-4626157/25000000 : ℝ)|=(4626157/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219322487/10000000000 : ℝ)|^4545 ≤ (8640101450527/20000000000000 : ℝ)^3521
        have hw : |(5219322487/10000000000 : ℝ)|=(5219322487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715282977/5000000000 : ℝ)|^4545 ≤ (5683829475603/12500000000000 : ℝ)^3521
        have hw : |(2715282977/5000000000 : ℝ)|=(2715282977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s6_2 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323695349/2500000000 : ℝ)*x 0 + (-174738419/1000000000 : ℝ)*x 1 + (5430565963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323695349/2500000000 : ℝ)^4545 ≤ (687631493159/1562500000000 : ℝ)^3521 := by
    have hnat : (1323695349 : ℕ)^4545*1562500000000^3521 ≤ 687631493159^3521*2500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323695349 2500000000 687631493159 1562500000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174738419/1000000000 : ℝ)^4545 ≤ (2630237129523/25000000000000 : ℝ)^3521 := by
    have hnat : (174738419 : ℕ)^4545*25000000000000^3521 ≤ 2630237129523^3521*1000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174738419 1000000000 2630237129523 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430565963/10000000000 : ℝ)^4545 ≤ (22735317951049/50000000000000 : ℝ)^3521 := by
    have hnat : (5430565963 : ℕ)^4545*50000000000000^3521 ≤ 22735317951049^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430565963 10000000000 22735317951049 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323695349/2500000000 : ℝ), (-174738419/1000000000 : ℝ), (5430565963/10000000000 : ℝ)] ![(687631493159/1562500000000 : ℝ), (2630237129523/25000000000000 : ℝ), (22735317951049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323695349/2500000000 : ℝ)|^4545 ≤ (687631493159/1562500000000 : ℝ)^3521
        have hw : |(1323695349/2500000000 : ℝ)|=(1323695349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174738419/1000000000 : ℝ)|^4545 ≤ (2630237129523/25000000000000 : ℝ)^3521
        have hw : |(-174738419/1000000000 : ℝ)|=(174738419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430565963/10000000000 : ℝ)|^4545 ≤ (22735317951049/50000000000000 : ℝ)^3521
        have hw : |(5430565963/10000000000 : ℝ)|=(5430565963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s6_3 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294781407/10000000000 : ℝ)*x 0 + (5430565957/10000000000 : ℝ)*x 1 + (-218423023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294781407/10000000000 : ℝ)^4545 ≤ (22004207840097/50000000000000 : ℝ)^3521 := by
    have hnat : (5294781407 : ℕ)^4545*50000000000000^3521 ≤ 22004207840097^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294781407 10000000000 22004207840097 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430565957/10000000000 : ℝ)^4545 ≤ (45470635837249/100000000000000 : ℝ)^3521 := by
    have hnat : (5430565957 : ℕ)^4545*100000000000000^3521 ≤ 45470635837249^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430565957 10000000000 45470635837249 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218423023/1250000000 : ℝ)^4545 ≤ (526047423573/5000000000000 : ℝ)^3521 := by
    have hnat : (218423023 : ℕ)^4545*5000000000000^3521 ≤ 526047423573^3521*1250000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218423023 1250000000 526047423573 5000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294781407/10000000000 : ℝ), (5430565957/10000000000 : ℝ), (-218423023/1250000000 : ℝ)] ![(22004207840097/50000000000000 : ℝ), (45470635837249/100000000000000 : ℝ), (526047423573/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294781407/10000000000 : ℝ)|^4545 ≤ (22004207840097/50000000000000 : ℝ)^3521
        have hw : |(5294781407/10000000000 : ℝ)|=(5294781407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430565957/10000000000 : ℝ)|^4545 ≤ (45470635837249/100000000000000 : ℝ)^3521
        have hw : |(5430565957/10000000000 : ℝ)|=(5430565957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218423023/1250000000 : ℝ)|^4545 ≤ (526047423573/5000000000000 : ℝ)^3521
        have hw : |(-218423023/1250000000 : ℝ)|=(218423023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s6_4 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170571263/400000000 : ℝ)*x 0 + (225581499/500000000 : ℝ)*x 1 + (4028564203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170571263/400000000 : ℝ)^4545 ≤ (33280914860703/100000000000000 : ℝ)^3521 := by
    have hnat : (170571263 : ℕ)^4545*100000000000000^3521 ≤ 33280914860703^3521*400000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170571263 400000000 33280914860703 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225581499/500000000 : ℝ)^4545 ≤ (35793527302553/100000000000000 : ℝ)^3521 := by
    have hnat : (225581499 : ℕ)^4545*100000000000000^3521 ≤ 35793527302553^3521*500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225581499 500000000 35793527302553 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028564203/10000000000 : ℝ)^4545 ≤ (30925557818001/100000000000000 : ℝ)^3521 := by
    have hnat : (4028564203 : ℕ)^4545*100000000000000^3521 ≤ 30925557818001^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028564203 10000000000 30925557818001 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170571263/400000000 : ℝ), (225581499/500000000 : ℝ), (4028564203/10000000000 : ℝ)] ![(33280914860703/100000000000000 : ℝ), (35793527302553/100000000000000 : ℝ), (30925557818001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170571263/400000000 : ℝ)|^4545 ≤ (33280914860703/100000000000000 : ℝ)^3521
        have hw : |(170571263/400000000 : ℝ)|=(170571263/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225581499/500000000 : ℝ)|^4545 ≤ (35793527302553/100000000000000 : ℝ)^3521
        have hw : |(225581499/500000000 : ℝ)|=(225581499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028564203/10000000000 : ℝ)|^4545 ≤ (30925557818001/100000000000000 : ℝ)^3521
        have hw : |(4028564203/10000000000 : ℝ)|=(4028564203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1524_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10961/100000 : ℝ) ^ (4543/1024 : ℝ) ≤ (109977237304289/2000000000000000000 : ℝ) := by
    have hpowers : (10961/100000 : ℝ)^4543 ≤ (109977237304289/2000000000000000000 : ℝ)^1024 := by
      have hnat : (10961 : ℕ)^4543*2000000000000000000^1024 ≤ 109977237304289^1024*100000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10961 100000 109977237304289 2000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10961/100000 : ℝ)) (X := (109977237304289/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4543/1024 : ℝ) ≤ (25462301947812919/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4543 ≤ (25462301947812919/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4543*100000000000000000000^1024 ≤ 25462301947812919^1024*25000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 25462301947812919 100000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (25462301947812919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000109977237304289/1000000000000000000 : ℝ) ≤ (10000247880023127/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (1000109977237304289/1000000000000000000 : ℝ)^1024 ≤ (10000247880023127/10000000000000000 : ℝ)^4543 := by
      have hnat : (1000109977237304289 : ℕ)^1024*10000000000000000^4543 ≤ 10000247880023127^4543*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000109977237304289 1000000000000000000 10000247880023127 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000247880023127/10000000000000000 : ℝ)) (X := (1000109977237304289/1000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030961163813027369/100000000000000000000 : ℝ) ≤ (1000069778628027/1000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (100030961163813027369/100000000000000000000 : ℝ)^1024 ≤ (1000069778628027/1000000000000000 : ℝ)^4543 := by
      have hnat : (100030961163813027369 : ℕ)^1024*1000000000000000^4543 ≤ 1000069778628027^4543*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030961163813027369 100000000000000000000 1000069778628027 1000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000069778628027/1000000000000000 : ℝ)) (X := (100030961163813027369/100000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025462301947812919/50000000000000000000 : ℝ) ≤ (10001147692537413/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (50025462301947812919/50000000000000000000 : ℝ)^1024 ≤ (10001147692537413/10000000000000000 : ℝ)^4543 := by
      have hnat : (50025462301947812919 : ℕ)^1024*10000000000000000^4543 ≤ 10001147692537413^4543*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025462301947812919 50000000000000000000 10001147692537413 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001147692537413/10000000000000000 : ℝ)) (X := (50025462301947812919/50000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109977237304289/2000000000000000000 : ℝ) ≤ ((1808850332655020583/1809200000000000000 : ℝ)+2*(449906257143/452300000000000 : ℝ)*(10961/100000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (1808850332655020583/1809200000000000000 : ℝ)+2*(449906257143/452300000000000 : ℝ)*(10961/100000 : ℝ)=(10000247880023127/10000000000000000 : ℝ) by norm_num, show 1+2*(109977237304289/2000000000000000000 : ℝ)=(1000109977237304289/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25462301947812919/100000000000000000000 : ℝ)+(109977237304289/2000000000000000000 : ℝ) ≤ ((1808850332655020583/1809200000000000000 : ℝ)+(449906257143/452300000000000 : ℝ)*((3871/25000 : ℝ)+(10961/100000 : ℝ)))^(4543/1024 : ℝ) := by
    rw [show (1808850332655020583/1809200000000000000 : ℝ)+(449906257143/452300000000000 : ℝ)*((3871/25000 : ℝ)+(10961/100000 : ℝ))=(1000069778628027/1000000000000000 : ℝ) by norm_num, show 1+(25462301947812919/100000000000000000000 : ℝ)+(109977237304289/2000000000000000000 : ℝ)=(100030961163813027369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25462301947812919/100000000000000000000 : ℝ) ≤ ((1808850332655020583/1809200000000000000 : ℝ)+2*(449906257143/452300000000000 : ℝ)*(3871/25000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (1808850332655020583/1809200000000000000 : ℝ)+2*(449906257143/452300000000000 : ℝ)*(3871/25000 : ℝ)=(10001147692537413/10000000000000000 : ℝ) by norm_num, show 1+2*(25462301947812919/100000000000000000000 : ℝ)=(50025462301947812919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1808850332655020583/1809200000000000000 : ℝ)*(X 1 0+X 2 0)+(449906257143/452300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1808850332655020583/1809200000000000000 : ℝ)) (alpha := (449906257143/452300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1808850332655020583/1809200000000000000 : ℝ)*(X 0 1+X 2 1)+(449906257143/452300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1808850332655020583/1809200000000000000 : ℝ)) (alpha := (449906257143/452300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1808850332655020583/1809200000000000000 : ℝ)*(X 0 2+X 1 2)+(449906257143/452300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1808850332655020583/1809200000000000000 : ℝ)) (alpha := (449906257143/452300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((167216091/312500000 : ℝ)*X 2 0+(652277667/1250000000 : ℝ)*X 2 1+(-1959728971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-4626157/25000000 : ℝ)*X 0 0+(5219322487/10000000000 : ℝ)*X 0 1+(2715282977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323695349/2500000000 : ℝ)*X 1 0+(-174738419/1000000000 : ℝ)*X 1 1+(5430565963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294781407/10000000000 : ℝ)*X 2 0+(5430565957/10000000000 : ℝ)*X 2 1+(-218423023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((170571263/400000000 : ℝ)*X 0 0+(225581499/500000000 : ℝ)*X 0 1+(4028564203/10000000000 : ℝ)*X 0 2+(170571263/400000000 : ℝ)*X 1 0+(225581499/500000000 : ℝ)*X 1 1+(4028564203/10000000000 : ℝ)*X 1 2+(170571263/400000000 : ℝ)*X 2 0+(225581499/500000000 : ℝ)*X 2 1+(4028564203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47635163433232630027124127/11307500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44127001/6250000000000 : ℝ)*(base19) + (156754921/20000000000000 : ℝ)*(base23) + (117209683/50000000000000 : ℝ)*(lower1) + (46228893/50000000000000 : ℝ)*(upper3) + (30178641/100000000000000 : ℝ)*(lower4) + (23733497/25000000000000 : ℝ)*(upper5) + (425248081088623/12500000000000 : ℝ)*(major0) + (425248081088623/12500000000000 : ℝ)*(major1) + (425248081088623/12500000000000 : ℝ)*(major2) + (4020209/390625000000 : ℝ)*(sp0) + (4733862715249911/100000000000000 : ℝ)*(sp1) + (591732751152237/12500000000000 : ℝ)*(sp2) + (4733860902301803/100000000000000 : ℝ)*(sp3) + (2070106441744541/100000000000000 : ℝ)*(sp4) + (2070106441744541/100000000000000 : ℝ)*(f.failure) + (4733862715249911/100000000000000 : ℝ)*(f.sum) + (32907697361413/22615000000000000000000000000 : ℝ)*base66 + (537249367314728209/22615000000000000000000000000000 : ℝ)*base67 + (147096545914471791/22615000000000000000000000000000 : ℝ)*base70 + (214138690211481791/22615000000000000000000000000000 : ℝ)*base72 + (20566755626153/5653750000000000000000000000 : ℝ)*base73 + (418505876088818209/22615000000000000000000000000000 : ℝ)*base75 + (64083770054076791/22615000000000000000000000000000 : ℝ)*base78 + (435719241353441791/22615000000000000000000000000000 : ℝ)*base80 + (35442150581207/22615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22448497/5000000000000000000000 : ℝ)*base89 + (22448497/5000000000000000000000 : ℝ)*base91 + (22448497/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1524_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1524_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1524_s7_0 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-925218217/5000000000 : ℝ)*x 0 + (5431671571/10000000000 : ℝ)*x 1 + (2609111737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925218217/5000000000 : ℝ)^4545 ≤ (11328648571471/100000000000000 : ℝ)^3521 := by
    have hnat : (925218217 : ℕ)^4545*100000000000000^3521 ≤ 11328648571471^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925218217 5000000000 11328648571471 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431671571/10000000000 : ℝ)^4545 ≤ (45482585899913/100000000000000 : ℝ)^3521 := by
    have hnat : (5431671571 : ℕ)^4545*100000000000000^3521 ≤ 45482585899913^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431671571 10000000000 45482585899913 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609111737/5000000000 : ℝ)^4545 ≤ (4318876552213/10000000000000 : ℝ)^3521 := by
    have hnat : (2609111737 : ℕ)^4545*10000000000000^3521 ≤ 4318876552213^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609111737 5000000000 4318876552213 10000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925218217/5000000000 : ℝ), (5431671571/10000000000 : ℝ), (2609111737/5000000000 : ℝ)] ![(11328648571471/100000000000000 : ℝ), (45482585899913/100000000000000 : ℝ), (4318876552213/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925218217/5000000000 : ℝ)|^4545 ≤ (11328648571471/100000000000000 : ℝ)^3521
        have hw : |(-925218217/5000000000 : ℝ)|=(925218217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431671571/10000000000 : ℝ)|^4545 ≤ (45482585899913/100000000000000 : ℝ)^3521
        have hw : |(5431671571/10000000000 : ℝ)|=(5431671571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609111737/5000000000 : ℝ)|^4545 ≤ (4318876552213/10000000000000 : ℝ)^3521
        have hw : |(2609111737/5000000000 : ℝ)|=(2609111737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s7_1 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334432099/625000000 : ℝ)*x 0 + (-1959727927/10000000000 : ℝ)*x 1 + (2609111729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334432099/625000000 : ℝ)^4545 ≤ (44611578782841/100000000000000 : ℝ)^3521 := by
    have hnat : (334432099 : ℕ)^4545*100000000000000^3521 ≤ 44611578782841^3521*625000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334432099 625000000 44611578782841 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959727927/10000000000 : ℝ)^4545 ≤ (6099827924311/50000000000000 : ℝ)^3521 := by
    have hnat : (1959727927 : ℕ)^4545*50000000000000^3521 ≤ 6099827924311^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959727927 10000000000 6099827924311 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609111729/5000000000 : ℝ)^4545 ≤ (43188765351193/100000000000000 : ℝ)^3521 := by
    have hnat : (2609111729 : ℕ)^4545*100000000000000^3521 ≤ 43188765351193^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609111729 5000000000 43188765351193 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334432099/625000000 : ℝ), (-1959727927/10000000000 : ℝ), (2609111729/5000000000 : ℝ)] ![(44611578782841/100000000000000 : ℝ), (6099827924311/50000000000000 : ℝ), (43188765351193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334432099/625000000 : ℝ)|^4545 ≤ (44611578782841/100000000000000 : ℝ)^3521
        have hw : |(334432099/625000000 : ℝ)|=(334432099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959727927/10000000000 : ℝ)|^4545 ≤ (6099827924311/50000000000000 : ℝ)^3521
        have hw : |(-1959727927/10000000000 : ℝ)|=(1959727927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609111729/5000000000 : ℝ)|^4545 ≤ (43188765351193/100000000000000 : ℝ)^3521
        have hw : |(2609111729/5000000000 : ℝ)|=(2609111729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s7_2 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675456757/5000000000 : ℝ)*x 0 + (521822351/1000000000 : ℝ)*x 1 + (-1959727953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675456757/5000000000 : ℝ)^4545 ≤ (4461157802951/10000000000000 : ℝ)^3521 := by
    have hnat : (2675456757 : ℕ)^4545*10000000000000^3521 ≤ 4461157802951^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675456757 5000000000 4461157802951 10000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521822351/1000000000 : ℝ)^4545 ≤ (21594382953369/50000000000000 : ℝ)^3521 := by
    have hnat : (521822351 : ℕ)^4545*50000000000000^3521 ≤ 21594382953369^3521*1000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521822351 1000000000 21594382953369 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959727953/10000000000 : ℝ)^4545 ≤ (3049914014387/25000000000000 : ℝ)^3521 := by
    have hnat : (1959727953 : ℕ)^4545*25000000000000^3521 ≤ 3049914014387^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959727953 10000000000 3049914014387 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675456757/5000000000 : ℝ), (521822351/1000000000 : ℝ), (-1959727953/10000000000 : ℝ)] ![(4461157802951/10000000000000 : ℝ), (21594382953369/50000000000000 : ℝ), (3049914014387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675456757/5000000000 : ℝ)|^4545 ≤ (4461157802951/10000000000000 : ℝ)^3521
        have hw : |(2675456757/5000000000 : ℝ)|=(2675456757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521822351/1000000000 : ℝ)|^4545 ≤ (21594382953369/50000000000000 : ℝ)^3521
        have hw : |(521822351/1000000000 : ℝ)|=(521822351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959727953/10000000000 : ℝ)|^4545 ≤ (3049914014387/25000000000000 : ℝ)^3521
        have hw : |(-1959727953/10000000000 : ℝ)|=(1959727953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s7_3 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4264216659/10000000000 : ℝ)*x 0 + (4026034141/10000000000 : ℝ)*x 1 + (4514141503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264216659/10000000000 : ℝ)^4545 ≤ (3328026087533/10000000000000 : ℝ)^3521 := by
    have hnat : (4264216659 : ℕ)^4545*10000000000000^3521 ≤ 3328026087533^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264216659 10000000000 3328026087533 10000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026034141/10000000000 : ℝ)^4545 ≤ (7725122354589/25000000000000 : ℝ)^3521 := by
    have hnat : (4026034141 : ℕ)^4545*25000000000000^3521 ≤ 7725122354589^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026034141 10000000000 7725122354589 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514141503/10000000000 : ℝ)^4545 ≤ (35819249685289/100000000000000 : ℝ)^3521 := by
    have hnat : (4514141503 : ℕ)^4545*100000000000000^3521 ≤ 35819249685289^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514141503 10000000000 35819249685289 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264216659/10000000000 : ℝ), (4026034141/10000000000 : ℝ), (4514141503/10000000000 : ℝ)] ![(3328026087533/10000000000000 : ℝ), (7725122354589/25000000000000 : ℝ), (35819249685289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264216659/10000000000 : ℝ)|^4545 ≤ (3328026087533/10000000000000 : ℝ)^3521
        have hw : |(4264216659/10000000000 : ℝ)|=(4264216659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026034141/10000000000 : ℝ)|^4545 ≤ (7725122354589/25000000000000 : ℝ)^3521
        have hw : |(4026034141/10000000000 : ℝ)|=(4026034141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514141503/10000000000 : ℝ)|^4545 ≤ (35819249685289/100000000000000 : ℝ)^3521
        have hw : |(4514141503/10000000000 : ℝ)|=(4514141503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s7_4 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-370092619/2000000000 : ℝ)*x 0 + (5219326403/10000000000 : ℝ)*x 1 + (5430561867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370092619/2000000000 : ℝ)^4545 ≤ (5664429632001/50000000000000 : ℝ)^3521 := by
    have hnat : (370092619 : ℕ)^4545*50000000000000^3521 ≤ 5664429632001^3521*2000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370092619 2000000000 5664429632001 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219326403/10000000000 : ℝ)^4545 ≤ (21600274546011/50000000000000 : ℝ)^3521 := by
    have hnat : (5219326403 : ℕ)^4545*50000000000000^3521 ≤ 21600274546011^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219326403 10000000000 21600274546011 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430561867/10000000000 : ℝ)^4545 ≤ (5683823953959/12500000000000 : ℝ)^3521 := by
    have hnat : (5430561867 : ℕ)^4545*12500000000000^3521 ≤ 5683823953959^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430561867 10000000000 5683823953959 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370092619/2000000000 : ℝ), (5219326403/10000000000 : ℝ), (5430561867/10000000000 : ℝ)] ![(5664429632001/50000000000000 : ℝ), (21600274546011/50000000000000 : ℝ), (5683823953959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370092619/2000000000 : ℝ)|^4545 ≤ (5664429632001/50000000000000 : ℝ)^3521
        have hw : |(-370092619/2000000000 : ℝ)|=(370092619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219326403/10000000000 : ℝ)|^4545 ≤ (21600274546011/50000000000000 : ℝ)^3521
        have hw : |(5219326403/10000000000 : ℝ)|=(5219326403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430561867/10000000000 : ℝ)|^4545 ≤ (5683823953959/12500000000000 : ℝ)^3521
        have hw : |(5430561867/10000000000 : ℝ)|=(5430561867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_s7_5 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213213759/500000000 : ℝ)*x 0 + (451162773/1000000000 : ℝ)*x 1 + (4028573031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213213759/500000000 : ℝ)^4545 ≤ (33280850435217/100000000000000 : ℝ)^3521 := by
    have hnat : (213213759 : ℕ)^4545*100000000000000^3521 ≤ 33280850435217^3521*500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213213759 500000000 33280850435217 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451162773/1000000000 : ℝ)^4545 ≤ (35793504260489/100000000000000 : ℝ)^3521 := by
    have hnat : (451162773 : ℕ)^4545*100000000000000^3521 ≤ 35793504260489^3521*1000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451162773 1000000000 35793504260489 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028573031/10000000000 : ℝ)^4545 ≤ (15462822647873/50000000000000 : ℝ)^3521 := by
    have hnat : (4028573031 : ℕ)^4545*50000000000000^3521 ≤ 15462822647873^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028573031 10000000000 15462822647873 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213213759/500000000 : ℝ), (451162773/1000000000 : ℝ), (4028573031/10000000000 : ℝ)] ![(33280850435217/100000000000000 : ℝ), (35793504260489/100000000000000 : ℝ), (15462822647873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213213759/500000000 : ℝ)|^4545 ≤ (33280850435217/100000000000000 : ℝ)^3521
        have hw : |(213213759/500000000 : ℝ)|=(213213759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451162773/1000000000 : ℝ)|^4545 ≤ (35793504260489/100000000000000 : ℝ)^3521
        have hw : |(451162773/1000000000 : ℝ)|=(451162773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028573031/10000000000 : ℝ)|^4545 ≤ (15462822647873/50000000000000 : ℝ)^3521
        have hw : |(4028573031/10000000000 : ℝ)|=(4028573031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1524_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5481/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10961/100000 : ℝ) ^ (4543/1024 : ℝ) ≤ (109977237304289/2000000000000000000 : ℝ) := by
    have hpowers : (10961/100000 : ℝ)^4543 ≤ (109977237304289/2000000000000000000 : ℝ)^1024 := by
      have hnat : (10961 : ℕ)^4543*2000000000000000000^1024 ≤ 109977237304289^1024*100000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10961 100000 109977237304289 2000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10961/100000 : ℝ)) (X := (109977237304289/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4543/1024 : ℝ) ≤ (25455007220069491/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4543 ≤ (25455007220069491/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4543*100000000000000000000^1024 ≤ 25455007220069491^1024*100000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 25455007220069491 100000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (25455007220069491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000109977237304289/1000000000000000000 : ℝ) ≤ (10000247880023127/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (1000109977237304289/1000000000000000000 : ℝ)^1024 ≤ (10000247880023127/10000000000000000 : ℝ)^4543 := by
      have hnat : (1000109977237304289 : ℕ)^1024*10000000000000000^4543 ≤ 10000247880023127^4543*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000109977237304289 1000000000000000000 10000247880023127 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000247880023127/10000000000000000 : ℝ)) (X := (1000109977237304289/1000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030953869085283941/100000000000000000000 : ℝ) ≤ (10000697621895271/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (100030953869085283941/100000000000000000000 : ℝ)^1024 ≤ (10000697621895271/10000000000000000 : ℝ)^4543 := by
      have hnat : (100030953869085283941 : ℕ)^1024*10000000000000000^4543 ≤ 10000697621895271^4543*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030953869085283941 100000000000000000000 10000697621895271 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000697621895271/10000000000000000 : ℝ)) (X := (100030953869085283941/100000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025455007220069491/50000000000000000000 : ℝ) ≤ (2000229472753483/2000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (50025455007220069491/50000000000000000000 : ℝ)^1024 ≤ (2000229472753483/2000000000000000 : ℝ)^4543 := by
      have hnat : (50025455007220069491 : ℕ)^1024*2000000000000000^4543 ≤ 2000229472753483^4543*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025455007220069491 50000000000000000000 2000229472753483 2000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000229472753483/2000000000000000 : ℝ)) (X := (50025455007220069491/50000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109977237304289/2000000000000000000 : ℝ) ≤ ((22605630836071719763/22610000000000000000 : ℝ)+2*(28108867009/28262500000000 : ℝ)*(10961/100000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (22605630836071719763/22610000000000000000 : ℝ)+2*(28108867009/28262500000000 : ℝ)*(10961/100000 : ℝ)=(10000247880023127/10000000000000000 : ℝ) by norm_num, show 1+2*(109977237304289/2000000000000000000 : ℝ)=(1000109977237304289/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25455007220069491/100000000000000000000 : ℝ)+(109977237304289/2000000000000000000 : ℝ) ≤ ((22605630836071719763/22610000000000000000 : ℝ)+(28108867009/28262500000000 : ℝ)*((15483/100000 : ℝ)+(10961/100000 : ℝ)))^(4543/1024 : ℝ) := by
    rw [show (22605630836071719763/22610000000000000000 : ℝ)+(28108867009/28262500000000 : ℝ)*((15483/100000 : ℝ)+(10961/100000 : ℝ))=(10000697621895271/10000000000000000 : ℝ) by norm_num, show 1+(25455007220069491/100000000000000000000 : ℝ)+(109977237304289/2000000000000000000 : ℝ)=(100030953869085283941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25455007220069491/100000000000000000000 : ℝ) ≤ ((22605630836071719763/22610000000000000000 : ℝ)+2*(28108867009/28262500000000 : ℝ)*(15483/100000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (22605630836071719763/22610000000000000000 : ℝ)+2*(28108867009/28262500000000 : ℝ)*(15483/100000 : ℝ)=(2000229472753483/2000000000000000 : ℝ) by norm_num, show 1+2*(25455007220069491/100000000000000000000 : ℝ)=(50025455007220069491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22605630836071719763/22610000000000000000 : ℝ)*(X 1 0+X 2 0)+(28108867009/28262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22605630836071719763/22610000000000000000 : ℝ)) (alpha := (28108867009/28262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22605630836071719763/22610000000000000000 : ℝ)*(X 0 1+X 2 1)+(28108867009/28262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22605630836071719763/22610000000000000000 : ℝ)) (alpha := (28108867009/28262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22605630836071719763/22610000000000000000 : ℝ)*(X 0 2+X 1 2)+(28108867009/28262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22605630836071719763/22610000000000000000 : ℝ)) (alpha := (28108867009/28262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-925218217/5000000000 : ℝ)*X 0 0+(5431671571/10000000000 : ℝ)*X 0 1+(2609111737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334432099/625000000 : ℝ)*X 1 0+(-1959727927/10000000000 : ℝ)*X 1 1+(2609111729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675456757/5000000000 : ℝ)*X 2 0+(521822351/1000000000 : ℝ)*X 2 1+(-1959727953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4264216659/10000000000 : ℝ)*X 0 0+(4026034141/10000000000 : ℝ)*X 0 1+(4514141503/10000000000 : ℝ)*X 0 2+(4264216659/10000000000 : ℝ)*X 1 0+(4026034141/10000000000 : ℝ)*X 1 1+(4514141503/10000000000 : ℝ)*X 1 2+(4264216659/10000000000 : ℝ)*X 2 0+(4026034141/10000000000 : ℝ)*X 2 1+(4514141503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-370092619/2000000000 : ℝ)*X 0 0+(5219326403/10000000000 : ℝ)*X 0 1+(5430561867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((213213759/500000000 : ℝ)*X 0 0+(451162773/1000000000 : ℝ)*X 0 1+(4028573031/10000000000 : ℝ)*X 0 2+(213213759/500000000 : ℝ)*X 1 0+(451162773/1000000000 : ℝ)*X 1 1+(4028573031/10000000000 : ℝ)*X 1 2+(213213759/500000000 : ℝ)*X 2 0+(451162773/1000000000 : ℝ)*X 2 1+(4028573031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29650800515623204545903/11305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2828683/781250000000 : ℝ)*(base19) + (133286011/50000000000000 : ℝ)*(base23) + (7269853/25000000000000 : ℝ)*(lower2) + (927947/1562500000000 : ℝ)*(upper3) + (2154689/20000000000000 : ℝ)*(lower4) + (420857915577303/12500000000000 : ℝ)*(major0) + (420857915577303/12500000000000 : ℝ)*(major1) + (420857915577303/12500000000000 : ℝ)*(major2) + (2342493214705687/50000000000000 : ℝ)*(sp0) + (2342495535569599/50000000000000 : ℝ)*(sp1) + (23424955833193/500000000000 : ℝ)*(sp2) + (512183014002863/25000000000000 : ℝ)*(sp3) + (5003799247/100000000000000 : ℝ)*(sp4) + (768146991/25000000000000 : ℝ)*(sp5) + (256091891074927/12500000000000 : ℝ)*(f.failure) + (2342495716605311/50000000000000 : ℝ)*(f.sum) + (16136985818393/11305000000000000000000000000 : ℝ)*base65 + (99487525727152027/40375000000000000000000000000000 : ℝ)*base67 + (244570763337902027/40375000000000000000000000000000 : ℝ)*base69 + (154361665620222973/40375000000000000000000000000000 : ℝ)*base72 + (6477770321599/5652500000000000000000000000 : ℝ)*base73 + (284180206744222973/40375000000000000000000000000000 : ℝ)*base76 + (16788978121777027/40375000000000000000000000000000 : ℝ)*base77 + (166786362562222973/40375000000000000000000000000000 : ℝ)*base80 + (1629805605979/353281250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2585141/625000000000000000000 : ℝ)*base90 + (2585141/625000000000000000000 : ℝ)*base92 + (2585141/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1524_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1524_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1524_box_0 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-327786561/2000000000 : ℝ)*x 0 + (540153511/1000000000 : ℝ)*x 1 + (5401535089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327786561/2000000000 : ℝ)^4545 ≤ (9685783107383/100000000000000 : ℝ)^3521 := by
    have hnat : (327786561 : ℕ)^4545*100000000000000^3521 ≤ 9685783107383^3521*2000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327786561 2000000000 9685783107383 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540153511/1000000000 : ℝ)^4545 ≤ (22578554275193/50000000000000 : ℝ)^3521 := by
    have hnat : (540153511 : ℕ)^4545*50000000000000^3521 ≤ 22578554275193^3521*1000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540153511 1000000000 22578554275193 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401535089/10000000000 : ℝ)^4545 ≤ (45157108323767/100000000000000 : ℝ)^3521 := by
    have hnat : (5401535089 : ℕ)^4545*100000000000000^3521 ≤ 45157108323767^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401535089 10000000000 45157108323767 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327786561/2000000000 : ℝ), (540153511/1000000000 : ℝ), (5401535089/10000000000 : ℝ)] ![(9685783107383/100000000000000 : ℝ), (22578554275193/50000000000000 : ℝ), (45157108323767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327786561/2000000000 : ℝ)|^4545 ≤ (9685783107383/100000000000000 : ℝ)^3521
        have hw : |(-327786561/2000000000 : ℝ)|=(327786561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540153511/1000000000 : ℝ)|^4545 ≤ (22578554275193/50000000000000 : ℝ)^3521
        have hw : |(540153511/1000000000 : ℝ)|=(540153511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401535089/10000000000 : ℝ)|^4545 ≤ (45157108323767/100000000000000 : ℝ)^3521
        have hw : |(5401535089/10000000000 : ℝ)|=(5401535089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_1 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270915821/10000000000 : ℝ)*x 0 + (-1820210319/10000000000 : ℝ)*x 1 + (168797993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270915821/10000000000 : ℝ)^4545 ≤ (10938132995931/25000000000000 : ℝ)^3521 := by
    have hnat : (5270915821 : ℕ)^4545*25000000000000^3521 ≤ 10938132995931^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270915821 10000000000 10938132995931 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820210319/10000000000 : ℝ)^4545 ≤ (11090352263219/100000000000000 : ℝ)^3521 := by
    have hnat : (1820210319 : ℕ)^4545*100000000000000^3521 ≤ 11090352263219^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820210319 10000000000 11090352263219 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168797993/312500000 : ℝ)^4545 ≤ (22578557868721/50000000000000 : ℝ)^3521 := by
    have hnat : (168797993 : ℕ)^4545*50000000000000^3521 ≤ 22578557868721^3521*312500000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168797993 312500000 22578557868721 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270915821/10000000000 : ℝ), (-1820210319/10000000000 : ℝ), (168797993/312500000 : ℝ)] ![(10938132995931/25000000000000 : ℝ), (11090352263219/100000000000000 : ℝ), (22578557868721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270915821/10000000000 : ℝ)|^4545 ≤ (10938132995931/25000000000000 : ℝ)^3521
        have hw : |(5270915821/10000000000 : ℝ)|=(5270915821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820210319/10000000000 : ℝ)|^4545 ≤ (11090352263219/100000000000000 : ℝ)^3521
        have hw : |(-1820210319/10000000000 : ℝ)|=(1820210319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168797993/312500000 : ℝ)|^4545 ≤ (22578557868721/50000000000000 : ℝ)^3521
        have hw : |(168797993/312500000 : ℝ)|=(168797993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_2 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527091587/1000000000 : ℝ)*x 0 + (1350383843/2500000000 : ℝ)*x 1 + (-1820210807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527091587/1000000000 : ℝ)^4545 ≤ (43752532508751/100000000000000 : ℝ)^3521 := by
    have hnat : (527091587 : ℕ)^4545*100000000000000^3521 ≤ 43752532508751^3521*1000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527091587 1000000000 43752532508751 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350383843/2500000000 : ℝ)^4545 ≤ (45157111377727/100000000000000 : ℝ)^3521 := by
    have hnat : (1350383843 : ℕ)^4545*100000000000000^3521 ≤ 45157111377727^3521*2500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350383843 2500000000 45157111377727 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1820210807/10000000000 : ℝ)^4545 ≤ (11090356101277/100000000000000 : ℝ)^3521 := by
    have hnat : (1820210807 : ℕ)^4545*100000000000000^3521 ≤ 11090356101277^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820210807 10000000000 11090356101277 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527091587/1000000000 : ℝ), (1350383843/2500000000 : ℝ), (-1820210807/10000000000 : ℝ)] ![(43752532508751/100000000000000 : ℝ), (45157111377727/100000000000000 : ℝ), (11090356101277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527091587/1000000000 : ℝ)|^4545 ≤ (43752532508751/100000000000000 : ℝ)^3521
        have hw : |(527091587/1000000000 : ℝ)|=(527091587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350383843/2500000000 : ℝ)|^4545 ≤ (45157111377727/100000000000000 : ℝ)^3521
        have hw : |(1350383843/2500000000 : ℝ)|=(1350383843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1820210807/10000000000 : ℝ)|^4545 ≤ (11090356101277/100000000000000 : ℝ)^3521
        have hw : |(-1820210807/10000000000 : ℝ)|=(1820210807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_3 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (178669723/400000000 : ℝ)*x 0 + (2084929219/5000000000 : ℝ)*x 1 + (2084929503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178669723/400000000 : ℝ)^4545 ≤ (4416813850397/12500000000000 : ℝ)^3521 := by
    have hnat : (178669723 : ℕ)^4545*12500000000000^3521 ≤ 4416813850397^3521*400000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178669723 400000000 4416813850397 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084929219/5000000000 : ℝ)^4545 ≤ (16166370876037/50000000000000 : ℝ)^3521 := by
    have hnat : (2084929219 : ℕ)^4545*50000000000000^3521 ≤ 16166370876037^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084929219 5000000000 16166370876037 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084929503/5000000000 : ℝ)^4545 ≤ (6466549487433/20000000000000 : ℝ)^3521 := by
    have hnat : (2084929503 : ℕ)^4545*20000000000000^3521 ≤ 6466549487433^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084929503 5000000000 6466549487433 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(178669723/400000000 : ℝ), (2084929219/5000000000 : ℝ), (2084929503/5000000000 : ℝ)] ![(4416813850397/12500000000000 : ℝ), (16166370876037/50000000000000 : ℝ), (6466549487433/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(178669723/400000000 : ℝ)|^4545 ≤ (4416813850397/12500000000000 : ℝ)^3521
        have hw : |(178669723/400000000 : ℝ)|=(178669723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084929219/5000000000 : ℝ)|^4545 ≤ (16166370876037/50000000000000 : ℝ)^3521
        have hw : |(2084929219/5000000000 : ℝ)|=(2084929219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084929503/5000000000 : ℝ)|^4545 ≤ (6466549487433/20000000000000 : ℝ)^3521
        have hw : |(2084929503/5000000000 : ℝ)|=(2084929503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_4 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067365561/10000000000 : ℝ)*x 0 + (5243994797/10000000000 : ℝ)*x 1 + (1048799017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067365561/10000000000 : ℝ)^4545 ≤ (13071411921543/100000000000000 : ℝ)^3521 := by
    have hnat : (2067365561 : ℕ)^4545*100000000000000^3521 ≤ 13071411921543^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067365561 10000000000 13071411921543 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243994797/10000000000 : ℝ)^4545 ≤ (21732146243671/50000000000000 : ℝ)^3521 := by
    have hnat : (5243994797 : ℕ)^4545*50000000000000^3521 ≤ 21732146243671^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243994797 10000000000 21732146243671 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048799017/2000000000 : ℝ)^4545 ≤ (43464295568619/100000000000000 : ℝ)^3521 := by
    have hnat : (1048799017 : ℕ)^4545*100000000000000^3521 ≤ 43464295568619^3521*2000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048799017 2000000000 43464295568619 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067365561/10000000000 : ℝ), (5243994797/10000000000 : ℝ), (1048799017/2000000000 : ℝ)] ![(13071411921543/100000000000000 : ℝ), (21732146243671/50000000000000 : ℝ), (43464295568619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067365561/10000000000 : ℝ)|^4545 ≤ (13071411921543/100000000000000 : ℝ)^3521
        have hw : |(-2067365561/10000000000 : ℝ)|=(2067365561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243994797/10000000000 : ℝ)|^4545 ≤ (21732146243671/50000000000000 : ℝ)^3521
        have hw : |(5243994797/10000000000 : ℝ)|=(5243994797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048799017/2000000000 : ℝ)|^4545 ≤ (43464295568619/100000000000000 : ℝ)^3521
        have hw : |(1048799017/2000000000 : ℝ)|=(1048799017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_5 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380497791/10000000000 : ℝ)*x 0 + (-1885372559/10000000000 : ℝ)*x 1 + (5243994919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380497791/10000000000 : ℝ)^4545 ≤ (5616276955219/12500000000000 : ℝ)^3521 := by
    have hnat : (5380497791 : ℕ)^4545*12500000000000^3521 ≤ 5616276955219^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380497791 10000000000 5616276955219 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885372559/10000000000 : ℝ)^4545 ≤ (1450686318397/12500000000000 : ℝ)^3521 := by
    have hnat : (1885372559 : ℕ)^4545*12500000000000^3521 ≤ 1450686318397^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885372559 10000000000 1450686318397 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243994919/10000000000 : ℝ)^4545 ≤ (8692858758521/20000000000000 : ℝ)^3521 := by
    have hnat : (5243994919 : ℕ)^4545*20000000000000^3521 ≤ 8692858758521^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243994919 10000000000 8692858758521 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380497791/10000000000 : ℝ), (-1885372559/10000000000 : ℝ), (5243994919/10000000000 : ℝ)] ![(5616276955219/12500000000000 : ℝ), (1450686318397/12500000000000 : ℝ), (8692858758521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380497791/10000000000 : ℝ)|^4545 ≤ (5616276955219/12500000000000 : ℝ)^3521
        have hw : |(5380497791/10000000000 : ℝ)|=(5380497791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1885372559/10000000000 : ℝ)|^4545 ≤ (1450686318397/12500000000000 : ℝ)^3521
        have hw : |(-1885372559/10000000000 : ℝ)|=(1885372559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243994919/10000000000 : ℝ)|^4545 ≤ (8692858758521/20000000000000 : ℝ)^3521
        have hw : |(5243994919/10000000000 : ℝ)|=(5243994919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_6 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84070279/156250000 : ℝ)*x 0 + (5243994863/10000000000 : ℝ)*x 1 + (-471343137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84070279/156250000 : ℝ)^4545 ≤ (8986043268479/20000000000000 : ℝ)^3521 := by
    have hnat : (84070279 : ℕ)^4545*20000000000000^3521 ≤ 8986043268479^3521*156250000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84070279 156250000 8986043268479 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243994863/10000000000 : ℝ)^4545 ≤ (10866073298367/25000000000000 : ℝ)^3521 := by
    have hnat : (5243994863 : ℕ)^4545*25000000000000^3521 ≤ 10866073298367^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243994863 10000000000 10866073298367 25000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471343137/2500000000 : ℝ)^4545 ≤ (11605490459773/100000000000000 : ℝ)^3521 := by
    have hnat : (471343137 : ℕ)^4545*100000000000000^3521 ≤ 11605490459773^3521*2500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471343137 2500000000 11605490459773 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84070279/156250000 : ℝ), (5243994863/10000000000 : ℝ), (-471343137/2500000000 : ℝ)] ![(8986043268479/20000000000000 : ℝ), (10866073298367/25000000000000 : ℝ), (11605490459773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84070279/156250000 : ℝ)|^4545 ≤ (8986043268479/20000000000000 : ℝ)^3521
        have hw : |(84070279/156250000 : ℝ)|=(84070279/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243994863/10000000000 : ℝ)|^4545 ≤ (10866073298367/25000000000000 : ℝ)^3521
        have hw : |(5243994863/10000000000 : ℝ)|=(5243994863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471343137/2500000000 : ℝ)|^4545 ≤ (11605490459773/100000000000000 : ℝ)^3521
        have hw : |(-471343137/2500000000 : ℝ)|=(471343137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_7 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2029606403/5000000000 : ℝ)*x 0 + (4373490989/10000000000 : ℝ)*x 1 + (1093372799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029606403/5000000000 : ℝ)^4545 ≤ (15614796948609/50000000000000 : ℝ)^3521 := by
    have hnat : (2029606403 : ℕ)^4545*50000000000000^3521 ≤ 15614796948609^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029606403 5000000000 15614796948609 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4373490989/10000000000 : ℝ)^4545 ≤ (1375408079723/4000000000000 : ℝ)^3521 := by
    have hnat : (4373490989 : ℕ)^4545*4000000000000^3521 ≤ 1375408079723^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373490989 10000000000 1375408079723 4000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093372799/2500000000 : ℝ)^4545 ≤ (1719260204693/5000000000000 : ℝ)^3521 := by
    have hnat : (1093372799 : ℕ)^4545*5000000000000^3521 ≤ 1719260204693^3521*2500000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093372799 2500000000 1719260204693 5000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2029606403/5000000000 : ℝ), (4373490989/10000000000 : ℝ), (1093372799/2500000000 : ℝ)] ![(15614796948609/50000000000000 : ℝ), (1375408079723/4000000000000 : ℝ), (1719260204693/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2029606403/5000000000 : ℝ)|^4545 ≤ (15614796948609/50000000000000 : ℝ)^3521
        have hw : |(2029606403/5000000000 : ℝ)|=(2029606403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4373490989/10000000000 : ℝ)|^4545 ≤ (1375408079723/4000000000000 : ℝ)^3521
        have hw : |(4373490989/10000000000 : ℝ)|=(4373490989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093372799/2500000000 : ℝ)|^4545 ≤ (1719260204693/5000000000000 : ℝ)^3521
        have hw : |(1093372799/2500000000 : ℝ)|=(1093372799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_8 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976765549/10000000000 : ℝ)*x 0 + (2566747609/5000000000 : ℝ)*x 1 + (2710975813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976765549/10000000000 : ℝ)^4545 ≤ (1542092064349/12500000000000 : ℝ)^3521 := by
    have hnat : (1976765549 : ℕ)^4545*12500000000000^3521 ≤ 1542092064349^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976765549 10000000000 1542092064349 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566747609/5000000000 : ℝ)^4545 ≤ (528571395607/1250000000000 : ℝ)^3521 := by
    have hnat : (2566747609 : ℕ)^4545*1250000000000^3521 ≤ 528571395607^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566747609 5000000000 528571395607 1250000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710975813/5000000000 : ℝ)^4545 ≤ (45377551818123/100000000000000 : ℝ)^3521 := by
    have hnat : (2710975813 : ℕ)^4545*100000000000000^3521 ≤ 45377551818123^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710975813 5000000000 45377551818123 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976765549/10000000000 : ℝ), (2566747609/5000000000 : ℝ), (2710975813/5000000000 : ℝ)] ![(1542092064349/12500000000000 : ℝ), (528571395607/1250000000000 : ℝ), (45377551818123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976765549/10000000000 : ℝ)|^4545 ≤ (1542092064349/12500000000000 : ℝ)^3521
        have hw : |(-1976765549/10000000000 : ℝ)|=(1976765549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566747609/5000000000 : ℝ)|^4545 ≤ (528571395607/1250000000000 : ℝ)^3521
        have hw : |(2566747609/5000000000 : ℝ)|=(2566747609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710975813/5000000000 : ℝ)|^4545 ≤ (45377551818123/100000000000000 : ℝ)^3521
        have hw : |(2710975813/5000000000 : ℝ)|=(2710975813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_9 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256709327/10000000000 : ℝ)*x 0 + (-1811523331/10000000000 : ℝ)*x 1 + (33887197/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256709327/10000000000 : ℝ)^4545 ≤ (8720074324419/20000000000000 : ℝ)^3521 := by
    have hnat : (5256709327 : ℕ)^4545*20000000000000^3521 ≤ 8720074324419^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256709327 10000000000 8720074324419 20000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811523331/10000000000 : ℝ)^4545 ≤ (88176621497/800000000000 : ℝ)^3521 := by
    have hnat : (1811523331 : ℕ)^4545*800000000000^3521 ≤ 88176621497^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811523331 10000000000 88176621497 800000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33887197/62500000 : ℝ)^4545 ≤ (22688775336491/50000000000000 : ℝ)^3521 := by
    have hnat : (33887197 : ℕ)^4545*50000000000000^3521 ≤ 22688775336491^3521*62500000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33887197 62500000 22688775336491 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256709327/10000000000 : ℝ), (-1811523331/10000000000 : ℝ), (33887197/62500000 : ℝ)] ![(8720074324419/20000000000000 : ℝ), (88176621497/800000000000 : ℝ), (22688775336491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256709327/10000000000 : ℝ)|^4545 ≤ (8720074324419/20000000000000 : ℝ)^3521
        have hw : |(5256709327/10000000000 : ℝ)|=(5256709327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811523331/10000000000 : ℝ)|^4545 ≤ (88176621497/800000000000 : ℝ)^3521
        have hw : |(-1811523331/10000000000 : ℝ)|=(1811523331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33887197/62500000 : ℝ)|^4545 ≤ (22688775336491/50000000000000 : ℝ)^3521
        have hw : |(33887197/62500000 : ℝ)|=(33887197/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_10 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628354603/5000000000 : ℝ)*x 0 + (677743969/1250000000 : ℝ)*x 1 + (-1811523177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628354603/5000000000 : ℝ)^4545 ≤ (43600370326619/100000000000000 : ℝ)^3521 := by
    have hnat : (2628354603 : ℕ)^4545*100000000000000^3521 ≤ 43600370326619^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628354603 5000000000 43600370326619 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677743969/1250000000 : ℝ)^4545 ≤ (45377553179329/100000000000000 : ℝ)^3521 := by
    have hnat : (677743969 : ℕ)^4545*100000000000000^3521 ≤ 45377553179329^3521*1250000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677743969 1250000000 45377553179329 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811523177/10000000000 : ℝ)^4545 ≤ (11022076477619/100000000000000 : ℝ)^3521 := by
    have hnat : (1811523177 : ℕ)^4545*100000000000000^3521 ≤ 11022076477619^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811523177 10000000000 11022076477619 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628354603/5000000000 : ℝ), (677743969/1250000000 : ℝ), (-1811523177/10000000000 : ℝ)] ![(43600370326619/100000000000000 : ℝ), (45377553179329/100000000000000 : ℝ), (11022076477619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628354603/5000000000 : ℝ)|^4545 ≤ (43600370326619/100000000000000 : ℝ)^3521
        have hw : |(2628354603/5000000000 : ℝ)|=(2628354603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677743969/1250000000 : ℝ)|^4545 ≤ (45377553179329/100000000000000 : ℝ)^3521
        have hw : |(677743969/1250000000 : ℝ)|=(677743969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1811523177/10000000000 : ℝ)|^4545 ≤ (11022076477619/100000000000000 : ℝ)^3521
        have hw : |(-1811523177/10000000000 : ℝ)|=(1811523177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_11 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (903681421/2000000000 : ℝ)*x 0 + (2071718027/5000000000 : ℝ)*x 1 + (4143436383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903681421/2000000000 : ℝ)^4545 ≤ (17931473219169/50000000000000 : ℝ)^3521 := by
    have hnat : (903681421 : ℕ)^4545*50000000000000^3521 ≤ 17931473219169^3521*2000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903681421 2000000000 17931473219169 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071718027/5000000000 : ℝ)^4545 ≤ (16034262565721/50000000000000 : ℝ)^3521 := by
    have hnat : (2071718027 : ℕ)^4545*50000000000000^3521 ≤ 16034262565721^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071718027 5000000000 16034262565721 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143436383/10000000000 : ℝ)^4545 ≤ (32068528418309/100000000000000 : ℝ)^3521 := by
    have hnat : (4143436383 : ℕ)^4545*100000000000000^3521 ≤ 32068528418309^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143436383 10000000000 32068528418309 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903681421/2000000000 : ℝ), (2071718027/5000000000 : ℝ), (4143436383/10000000000 : ℝ)] ![(17931473219169/50000000000000 : ℝ), (16034262565721/50000000000000 : ℝ), (32068528418309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903681421/2000000000 : ℝ)|^4545 ≤ (17931473219169/50000000000000 : ℝ)^3521
        have hw : |(903681421/2000000000 : ℝ)|=(903681421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071718027/5000000000 : ℝ)|^4545 ≤ (16034262565721/50000000000000 : ℝ)^3521
        have hw : |(2071718027/5000000000 : ℝ)|=(2071718027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143436383/10000000000 : ℝ)|^4545 ≤ (32068528418309/100000000000000 : ℝ)^3521
        have hw : |(4143436383/10000000000 : ℝ)|=(4143436383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_12 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1729419113/10000000000 : ℝ)*x 0 + (5508523187/10000000000 : ℝ)*x 1 + (5228959651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729419113/10000000000 : ℝ)^4545 ≤ (5190766343753/50000000000000 : ℝ)^3521 := by
    have hnat : (1729419113 : ℕ)^4545*50000000000000^3521 ≤ 5190766343753^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729419113 10000000000 5190766343753 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508523187/10000000000 : ℝ)^4545 ≤ (23157483449049/50000000000000 : ℝ)^3521 := by
    have hnat : (5508523187 : ℕ)^4545*50000000000000^3521 ≤ 23157483449049^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508523187 10000000000 23157483449049 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228959651/10000000000 : ℝ)^4545 ≤ (43303500408799/100000000000000 : ℝ)^3521 := by
    have hnat : (5228959651 : ℕ)^4545*100000000000000^3521 ≤ 43303500408799^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228959651 10000000000 43303500408799 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1729419113/10000000000 : ℝ), (5508523187/10000000000 : ℝ), (5228959651/10000000000 : ℝ)] ![(5190766343753/50000000000000 : ℝ), (23157483449049/50000000000000 : ℝ), (43303500408799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1729419113/10000000000 : ℝ)|^4545 ≤ (5190766343753/50000000000000 : ℝ)^3521
        have hw : |(-1729419113/10000000000 : ℝ)|=(1729419113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508523187/10000000000 : ℝ)|^4545 ≤ (23157483449049/50000000000000 : ℝ)^3521
        have hw : |(5508523187/10000000000 : ℝ)|=(5508523187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228959651/10000000000 : ℝ)|^4545 ≤ (43303500408799/100000000000000 : ℝ)^3521
        have hw : |(5228959651/10000000000 : ℝ)|=(5228959651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_13 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390955369/10000000000 : ℝ)*x 0 + (-945707023/5000000000 : ℝ)*x 1 + (209158429/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390955369/10000000000 : ℝ)^4545 ≤ (5630371391253/12500000000000 : ℝ)^3521 := by
    have hnat : (5390955369 : ℕ)^4545*12500000000000^3521 ≤ 5630371391253^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390955369 10000000000 5630371391253 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945707023/5000000000 : ℝ)^4545 ≤ (1456689620597/12500000000000 : ℝ)^3521 := by
    have hnat : (945707023 : ℕ)^4545*12500000000000^3521 ≤ 1456689620597^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945707023 5000000000 1456689620597 12500000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209158429/400000000 : ℝ)^4545 ≤ (43303511889803/100000000000000 : ℝ)^3521 := by
    have hnat : (209158429 : ℕ)^4545*100000000000000^3521 ≤ 43303511889803^3521*400000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209158429 400000000 43303511889803 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390955369/10000000000 : ℝ), (-945707023/5000000000 : ℝ), (209158429/400000000 : ℝ)] ![(5630371391253/12500000000000 : ℝ), (1456689620597/12500000000000 : ℝ), (43303511889803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390955369/10000000000 : ℝ)|^4545 ≤ (5630371391253/12500000000000 : ℝ)^3521
        have hw : |(5390955369/10000000000 : ℝ)|=(5390955369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945707023/5000000000 : ℝ)|^4545 ≤ (1456689620597/12500000000000 : ℝ)^3521
        have hw : |(-945707023/5000000000 : ℝ)|=(945707023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209158429/400000000 : ℝ)|^4545 ≤ (43303511889803/100000000000000 : ℝ)^3521
        have hw : |(209158429/400000000 : ℝ)|=(209158429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_14 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390955429/10000000000 : ℝ)*x 0 + (5228960019/10000000000 : ℝ)*x 1 + (-945707457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390955429/10000000000 : ℝ)^4545 ≤ (45042971777137/100000000000000 : ℝ)^3521 := by
    have hnat : (5390955429 : ℕ)^4545*100000000000000^3521 ≤ 45042971777137^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390955429 10000000000 45042971777137 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228960019/10000000000 : ℝ)^4545 ≤ (433035043427/1000000000000 : ℝ)^3521 := by
    have hnat : (5228960019 : ℕ)^4545*1000000000000^3521 ≤ 433035043427^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228960019 10000000000 433035043427 1000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945707457/5000000000 : ℝ)^4545 ≤ (182086310439/1562500000000 : ℝ)^3521 := by
    have hnat : (945707457 : ℕ)^4545*1562500000000^3521 ≤ 182086310439^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945707457 5000000000 182086310439 1562500000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390955429/10000000000 : ℝ), (5228960019/10000000000 : ℝ), (-945707457/5000000000 : ℝ)] ![(45042971777137/100000000000000 : ℝ), (433035043427/1000000000000 : ℝ), (182086310439/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390955429/10000000000 : ℝ)|^4545 ≤ (45042971777137/100000000000000 : ℝ)^3521
        have hw : |(5390955429/10000000000 : ℝ)|=(5390955429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228960019/10000000000 : ℝ)|^4545 ≤ (433035043427/1000000000000 : ℝ)^3521
        have hw : |(5228960019/10000000000 : ℝ)|=(5228960019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945707457/5000000000 : ℝ)|^4545 ≤ (182086310439/1562500000000 : ℝ)^3521
        have hw : |(-945707457/5000000000 : ℝ)|=(945707457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1524_box_15 (p : ℝ) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4019457809/10000000000 : ℝ)*x 0 + (2196451137/5000000000 : ℝ)*x 1 + (2196450719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4019457809/10000000000 : ℝ)^4545 ≤ (15417675569/50000000000 : ℝ)^3521 := by
    have hnat : (4019457809 : ℕ)^4545*50000000000^3521 ≤ 15417675569^3521*10000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019457809 10000000000 15417675569 50000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196451137/5000000000 : ℝ)^4545 ≤ (34582328670961/100000000000000 : ℝ)^3521 := by
    have hnat : (2196451137 : ℕ)^4545*100000000000000^3521 ≤ 34582328670961^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196451137 5000000000 34582328670961 100000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196450719/5000000000 : ℝ)^4545 ≤ (17291160087849/50000000000000 : ℝ)^3521 := by
    have hnat : (2196450719 : ℕ)^4545*50000000000000^3521 ≤ 17291160087849^3521*5000000000^4545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196450719 5000000000 17291160087849 50000000000000 4545 3521 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4545/1024 : ℝ)) 4545 3521 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4019457809/10000000000 : ℝ), (2196451137/5000000000 : ℝ), (2196450719/5000000000 : ℝ)] ![(15417675569/50000000000 : ℝ), (34582328670961/100000000000000 : ℝ), (17291160087849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4019457809/10000000000 : ℝ)|^4545 ≤ (15417675569/50000000000 : ℝ)^3521
        have hw : |(4019457809/10000000000 : ℝ)|=(4019457809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2196451137/5000000000 : ℝ)|^4545 ≤ (34582328670961/100000000000000 : ℝ)^3521
        have hw : |(2196451137/5000000000 : ℝ)|=(2196451137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2196450719/5000000000 : ℝ)|^4545 ≤ (17291160087849/50000000000000 : ℝ)^3521
        have hw : |(2196450719/5000000000 : ℝ)|=(2196450719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1524_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15939/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14671/25000 : ℝ) ∧ (80447/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86079/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5481/50000 : ℝ) ^ (4543/1024 : ℝ) ≤ (1375271976981297/25000000000000000000 : ℝ) := by
    have hpowers : (5481/50000 : ℝ)^4543 ≤ (1375271976981297/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5481 : ℕ)^4543*25000000000000000000^1024 ≤ 1375271976981297^1024*50000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5481 50000 1375271976981297 25000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5481/50000 : ℝ)) (X := (1375271976981297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4543/1024 : ℝ) ≤ (25455007220069491/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4543 ≤ (25455007220069491/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4543*100000000000000000000^1024 ≤ 25455007220069491^1024*100000^4543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 25455007220069491 100000000000000000000 4543 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (25455007220069491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501375271976981297/12500000000000000000 : ℝ) ≤ (10000247980365347/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (12501375271976981297/12500000000000000000 : ℝ)^1024 ≤ (10000247980365347/10000000000000000 : ℝ)^4543 := by
      have hnat : (12501375271976981297 : ℕ)^1024*10000000000000000^4543 ≤ 10000247980365347^4543*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501375271976981297 12500000000000000000 10000247980365347 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000247980365347/10000000000000000 : ℝ)) (X := (12501375271976981297/12500000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030956095127994679/100000000000000000000 : ℝ) ≤ (10000697672058629/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (100030956095127994679/100000000000000000000 : ℝ)^1024 ≤ (10000697672058629/10000000000000000 : ℝ)^4543 := by
      have hnat : (100030956095127994679 : ℕ)^1024*10000000000000000^4543 ≤ 10000697672058629^4543*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030956095127994679 100000000000000000000 10000697672058629 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000697672058629/10000000000000000 : ℝ)) (X := (100030956095127994679/100000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025455007220069491/50000000000000000000 : ℝ) ≤ (10001147363751911/10000000000000000 : ℝ) ^ (4543/1024 : ℝ) := by
    have hpowers : (50025455007220069491/50000000000000000000 : ℝ)^1024 ≤ (10001147363751911/10000000000000000 : ℝ)^4543 := by
      have hnat : (50025455007220069491 : ℕ)^1024*10000000000000000^4543 ≤ 10001147363751911^4543*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025455007220069491 50000000000000000000 10001147363751911 10000000000000000 1024 4543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001147363751911/10000000000000000 : ℝ)) (X := (50025455007220069491/50000000000000000000 : ℝ)) (by norm_num) 4543 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1375271976981297/25000000000000000000 : ℝ) ≤ ((15067087359516073073/15070000000000000000 : ℝ)+2*(74948615547/75350000000000 : ℝ)*(5481/50000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (15067087359516073073/15070000000000000000 : ℝ)+2*(74948615547/75350000000000 : ℝ)*(5481/50000 : ℝ)=(10000247980365347/10000000000000000 : ℝ) by norm_num, show 1+2*(1375271976981297/25000000000000000000 : ℝ)=(12501375271976981297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25455007220069491/100000000000000000000 : ℝ)+(1375271976981297/25000000000000000000 : ℝ) ≤ ((15067087359516073073/15070000000000000000 : ℝ)+(74948615547/75350000000000 : ℝ)*((15483/100000 : ℝ)+(5481/50000 : ℝ)))^(4543/1024 : ℝ) := by
    rw [show (15067087359516073073/15070000000000000000 : ℝ)+(74948615547/75350000000000 : ℝ)*((15483/100000 : ℝ)+(5481/50000 : ℝ))=(10000697672058629/10000000000000000 : ℝ) by norm_num, show 1+(25455007220069491/100000000000000000000 : ℝ)+(1375271976981297/25000000000000000000 : ℝ)=(100030956095127994679/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25455007220069491/100000000000000000000 : ℝ) ≤ ((15067087359516073073/15070000000000000000 : ℝ)+2*(74948615547/75350000000000 : ℝ)*(15483/100000 : ℝ))^(4543/1024 : ℝ) := by
    rw [show (15067087359516073073/15070000000000000000 : ℝ)+2*(74948615547/75350000000000 : ℝ)*(15483/100000 : ℝ)=(10001147363751911/10000000000000000 : ℝ) by norm_num, show 1+2*(25455007220069491/100000000000000000000 : ℝ)=(50025455007220069491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15067087359516073073/15070000000000000000 : ℝ)*(X 1 0+X 2 0)+(74948615547/75350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (15067087359516073073/15070000000000000000 : ℝ)) (alpha := (74948615547/75350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15067087359516073073/15070000000000000000 : ℝ)*(X 0 1+X 2 1)+(74948615547/75350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (15067087359516073073/15070000000000000000 : ℝ)) (alpha := (74948615547/75350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15067087359516073073/15070000000000000000 : ℝ)*(X 0 2+X 1 2)+(74948615547/75350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4543/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (15067087359516073073/15070000000000000000 : ℝ)) (alpha := (74948615547/75350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-327786561/2000000000 : ℝ)*X 0 0+(540153511/1000000000 : ℝ)*X 0 1+(5401535089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270915821/10000000000 : ℝ)*X 1 0+(-1820210319/10000000000 : ℝ)*X 1 1+(168797993/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((527091587/1000000000 : ℝ)*X 2 0+(1350383843/2500000000 : ℝ)*X 2 1+(-1820210807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((178669723/400000000 : ℝ)*X 0 0+(2084929219/5000000000 : ℝ)*X 0 1+(2084929503/5000000000 : ℝ)*X 0 2+(178669723/400000000 : ℝ)*X 1 0+(2084929219/5000000000 : ℝ)*X 1 1+(2084929503/5000000000 : ℝ)*X 1 2+(178669723/400000000 : ℝ)*X 2 0+(2084929219/5000000000 : ℝ)*X 2 1+(2084929503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2067365561/10000000000 : ℝ)*X 0 0+(5243994797/10000000000 : ℝ)*X 0 1+(1048799017/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380497791/10000000000 : ℝ)*X 1 0+(-1885372559/10000000000 : ℝ)*X 1 1+(5243994919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((84070279/156250000 : ℝ)*X 2 0+(5243994863/10000000000 : ℝ)*X 2 1+(-471343137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2029606403/5000000000 : ℝ)*X 0 0+(4373490989/10000000000 : ℝ)*X 0 1+(1093372799/2500000000 : ℝ)*X 0 2+(2029606403/5000000000 : ℝ)*X 1 0+(4373490989/10000000000 : ℝ)*X 1 1+(1093372799/2500000000 : ℝ)*X 1 2+(2029606403/5000000000 : ℝ)*X 2 0+(4373490989/10000000000 : ℝ)*X 2 1+(1093372799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1976765549/10000000000 : ℝ)*X 0 0+(2566747609/5000000000 : ℝ)*X 0 1+(2710975813/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256709327/10000000000 : ℝ)*X 1 0+(-1811523331/10000000000 : ℝ)*X 1 1+(33887197/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628354603/5000000000 : ℝ)*X 2 0+(677743969/1250000000 : ℝ)*X 2 1+(-1811523177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((903681421/2000000000 : ℝ)*X 0 0+(2071718027/5000000000 : ℝ)*X 0 1+(4143436383/10000000000 : ℝ)*X 0 2+(903681421/2000000000 : ℝ)*X 1 0+(2071718027/5000000000 : ℝ)*X 1 1+(4143436383/10000000000 : ℝ)*X 1 2+(903681421/2000000000 : ℝ)*X 2 0+(2071718027/5000000000 : ℝ)*X 2 1+(4143436383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1729419113/10000000000 : ℝ)*X 0 0+(5508523187/10000000000 : ℝ)*X 0 1+(5228959651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5390955369/10000000000 : ℝ)*X 1 0+(-945707023/5000000000 : ℝ)*X 1 1+(209158429/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5390955429/10000000000 : ℝ)*X 2 0+(5228960019/10000000000 : ℝ)*X 2 1+(-945707457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4019457809/10000000000 : ℝ)*X 0 0+(2196451137/5000000000 : ℝ)*X 0 1+(2196450719/5000000000 : ℝ)*X 0 2+(4019457809/10000000000 : ℝ)*X 1 0+(2196451137/5000000000 : ℝ)*X 1 1+(2196450719/5000000000 : ℝ)*X 1 2+(4019457809/10000000000 : ℝ)*X 2 0+(2196451137/5000000000 : ℝ)*X 2 1+(2196450719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1524_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15939/25000 : ℝ) ≤ (-480378986207137043788774692529197/753500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10824501/100000000000000 : ℝ)*(lower3) + (1791521/25000000000000 : ℝ)*(lower4) + (3725501/10000000000000 : ℝ)*(upper5) + (2241113775926337/100000000000000 : ℝ)*(major0) + (2241113775926337/100000000000000 : ℝ)*(major1) + (2241113775926337/100000000000000 : ℝ)*(major2) + (2401390191/100000000000000 : ℝ)*(sp1) + (2458864063/50000000000000 : ℝ)*(sp2) + (1546770129/100000000000000 : ℝ)*(sp3) + (392469915367507/12500000000000 : ℝ)*(sp4) + (392469903166399/12500000000000 : ℝ)*(sp5) + (3139756708993257/100000000000000 : ℝ)*(sp6) + (1363715384165501/100000000000000 : ℝ)*(sp7) + (2303781327/100000000000000 : ℝ)*(sp12) + (136371693093563/10000000000000 : ℝ)*(f.failure) + (3139761626721383/100000000000000 : ℝ)*(f.sum) + (1195450079211/941875000000000000000000000 : ℝ)*base65 + (7445277951978976399/1507000000000000000000000000000000 : ℝ)*base68 + (587125655323976399/1507000000000000000000000000000000 : ℝ)*base70 + (845121880722976399/1507000000000000000000000000000000 : ℝ)*base72 + (12294682263253/1883750000000000000000000000 : ℝ)*base74 + (1699781471012976399/1507000000000000000000000000000000 : ℝ)*base76 + (736914770274023601/1507000000000000000000000000000000 : ℝ)*base77 + (1425083967847023601/1507000000000000000000000000000000 : ℝ)*base79 + (13459886571/3767500000000000000000000000 : ℝ)*base82 + (3806471/500000000000000000000 : ℝ)*base89 + (3806471/500000000000000000000 : ℝ)*base91 + (3806471/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14671/25000 : ℝ) ≤ (44220451077874513059050289682677/75350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41465681/100000000000000 : ℝ)*(lower1) + (1938459/12500000000000 : ℝ)*(upper2) + (1225457/1250000000000 : ℝ)*(lower4) + (8188851/20000000000000 : ℝ)*(lower5) + (463636640387417/20000000000000 : ℝ)*(major0) + (463636640387417/20000000000000 : ℝ)*(major1) + (463636640387417/20000000000000 : ℝ)*(major2) + (641237158171201/20000000000000 : ℝ)*(sp0) + (3206173990945337/100000000000000 : ℝ)*(sp1) + (3206185786186253/100000000000000 : ℝ)*(sp2) + (705306824546529/50000000000000 : ℝ)*(sp3) + (103253077/625000000000 : ℝ)*(sp5) + (1181312851/25000000000000 : ℝ)*(sp6) + (1180145413/25000000000000 : ℝ)*(sp12) + (705306824546529/50000000000000 : ℝ)*(f.failure) + (3206190511437657/100000000000000 : ℝ)*(f.sum) + (2198930773631/301400000000000000000000000 : ℝ)*base65 + (162308410792322441/301400000000000000000000000000000 : ℝ)*base67 + (33417905578522441/301400000000000000000000000000000 : ℝ)*base69 + (854823537684277559/301400000000000000000000000000000 : ℝ)*base72 + (3614077104551/1507000000000000000000000000 : ℝ)*base73 + (210756935105522441/301400000000000000000000000000000 : ℝ)*base75 + (813551104823922441/301400000000000000000000000000000 : ℝ)*base77 + (346590912980722441/301400000000000000000000000000000 : ℝ)*base79 + (2966153359203/1507000000000000000000000000 : ℝ)*base81 + (2349307/2500000000000000000000 : ℝ)*base90 + (2349307/2500000000000000000000 : ℝ)*base92 + (2349307/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80447/100000 : ℝ) ≤ (75773667148175817081975609347979/94187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11982643/25000000000000 : ℝ)*(upper0) + (5125019/25000000000000 : ℝ)*(lower3) + (1564521/10000000000000 : ℝ)*(upper4) + (313828990263347/12500000000000 : ℝ)*(major0) + (313828990263347/12500000000000 : ℝ)*(major1) + (313828990263347/12500000000000 : ℝ)*(major2) + (40539161027/100000000000000 : ℝ)*(sp2) + (309943343/100000000000000 : ℝ)*(sp3) + (611480431/100000000000000 : ℝ)*(sp4) + (433340965509447/12500000000000 : ℝ)*(sp8) + (3466728613575497/100000000000000 : ℝ)*(sp9) + (346668807441447/10000000000000 : ℝ)*(sp10) + (2983824836969/195312500000 : ℝ)*(sp11) + (278019489/100000000000000 : ℝ)*(sp12) + (152771862647147/10000000000000 : ℝ)*(f.failure) + (3466728613575497/100000000000000 : ℝ)*(f.sum) + (146613226980811/7535000000000000000000000000 : ℝ)*base66 + (277835626228644669/188375000000000000000000000000000 : ℝ)*base68 + (407715473325644669/188375000000000000000000000000000 : ℝ)*base70 + (6413548454996144669/188375000000000000000000000000000 : ℝ)*base72 + (18497857961921/7535000000000000000000000000 : ℝ)*base74 + (1357784576729394669/188375000000000000000000000000000 : ℝ)*base76 + (2139291221000769669/188375000000000000000000000000000 : ℝ)*base78 + (1679853102073894669/188375000000000000000000000000000 : ℝ)*base80 + (2877403936839/7535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (988599/500000000000000000000 : ℝ)*base89 + (988599/500000000000000000000 : ℝ)*base91 + (988599/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-86079/100000 : ℝ) ≤ (-58962112159633931087210544182937/68500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3609539/12500000000000 : ℝ)*(lower0) + (9315883/50000000000000 : ℝ)*(lower1) + (349533173/100000000000000 : ℝ)*(upper3) + (117715087/100000000000000 : ℝ)*(lower4) + (2549998315712353/100000000000000 : ℝ)*(major0) + (2549998315712353/100000000000000 : ℝ)*(major1) + (2549998315712353/100000000000000 : ℝ)*(major2) + (927509463/100000000000000 : ℝ)*(sp0) + (133087457571/100000000000000 : ℝ)*(sp6) + (25858539103/25000000000000 : ℝ)*(sp7) + (894253666599791/25000000000000 : ℝ)*(sp12) + (1788507796954313/50000000000000 : ℝ)*(sp13) + (223555156653191/6250000000000 : ℝ)*(sp14) + (775784814370739/50000000000000 : ℝ)*(sp15) + (155167306289789/10000000000000 : ℝ)*(f.failure) + (1788507796954313/50000000000000 : ℝ)*(f.sum) + (2960796227567/685000000000000000000000000 : ℝ)*base65 + (610219523604639021/137000000000000000000000000000000 : ℝ)*base68 + (593350266682360979/137000000000000000000000000000000 : ℝ)*base69 + (1202253112385360979/137000000000000000000000000000000 : ℝ)*base71 + (1563287428789/342500000000000000000000000 : ℝ)*base74 + (483402988259360979/137000000000000000000000000000000 : ℝ)*base75 + (93602832963360979/137000000000000000000000000000000 : ℝ)*base77 + (543860318347639021/137000000000000000000000000000000 : ℝ)*base80 + (4433253131061/342500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1204113/500000000000000000000 : ℝ)*base89 + (1204113/500000000000000000000 : ℝ)*base91 + (1204113/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1524_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15939/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14671/25000 : ℝ) else (80447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86079/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1524_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1524_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15939/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14671/25000 : ℝ) else (80447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86079/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1524_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1524_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1524_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4543/1024 : ℝ) ≤ p) (hpb : p ≤ (4545/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82169317/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15939/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14671/25000 : ℝ) else (80447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86079/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1524_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
