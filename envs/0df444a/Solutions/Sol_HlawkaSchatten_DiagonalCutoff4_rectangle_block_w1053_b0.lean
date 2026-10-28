-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:57:08.070691+00:00
-- url     : https://prove2.me/submissions/041c22ec-ec4c-4de7-8d2e-bb9ade570354

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
theorem support_rectangle_w1053_s0_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480075721/2500000000 : ℝ)*x 0 + (3037564679/5000000000 : ℝ)*x 1 + (4769113853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480075721/2500000000 : ℝ)^4123 ≤ (5566012714407/50000000000000 : ℝ)^3099 := by
    have hnat : (480075721 : ℕ)^4123*50000000000000^3099 ≤ 5566012714407^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480075721 2500000000 5566012714407 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3037564679/5000000000 : ℝ)^4123 ≤ (25763565568853/50000000000000 : ℝ)^3099 := by
    have hnat : (3037564679 : ℕ)^4123*50000000000000^3099 ≤ 25763565568853^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037564679 5000000000 25763565568853 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769113853/10000000000 : ℝ)^4123 ≤ (18670421711537/50000000000000 : ℝ)^3099 := by
    have hnat : (4769113853 : ℕ)^4123*50000000000000^3099 ≤ 18670421711537^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769113853 10000000000 18670421711537 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480075721/2500000000 : ℝ), (3037564679/5000000000 : ℝ), (4769113853/10000000000 : ℝ)] ![(5566012714407/50000000000000 : ℝ), (25763565568853/50000000000000 : ℝ), (18670421711537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480075721/2500000000 : ℝ)|^4123 ≤ (5566012714407/50000000000000 : ℝ)^3099
        have hw : |(-480075721/2500000000 : ℝ)|=(480075721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3037564679/5000000000 : ℝ)|^4123 ≤ (25763565568853/50000000000000 : ℝ)^3099
        have hw : |(3037564679/5000000000 : ℝ)|=(3037564679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769113853/10000000000 : ℝ)|^4123 ≤ (18670421711537/50000000000000 : ℝ)^3099
        have hw : |(4769113853/10000000000 : ℝ)|=(4769113853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (220872137/400000000 : ℝ)*x 0 + (-2672442009/10000000000 : ℝ)*x 1 + (2384557393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220872137/400000000 : ℝ)^4123 ≤ (9075842631769/20000000000000 : ℝ)^3099 := by
    have hnat : (220872137 : ℕ)^4123*20000000000000^3099 ≤ 9075842631769^3099*400000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220872137 400000000 9075842631769 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2672442009/10000000000 : ℝ)^4123 ≤ (17279933685361/100000000000000 : ℝ)^3099 := by
    have hnat : (2672442009 : ℕ)^4123*100000000000000^3099 ≤ 17279933685361^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672442009 10000000000 17279933685361 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384557393/5000000000 : ℝ)^4123 ≤ (7468170628407/20000000000000 : ℝ)^3099 := by
    have hnat : (2384557393 : ℕ)^4123*20000000000000^3099 ≤ 7468170628407^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384557393 5000000000 7468170628407 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220872137/400000000 : ℝ), (-2672442009/10000000000 : ℝ), (2384557393/5000000000 : ℝ)] ![(9075842631769/20000000000000 : ℝ), (17279933685361/100000000000000 : ℝ), (7468170628407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220872137/400000000 : ℝ)|^4123 ≤ (9075842631769/20000000000000 : ℝ)^3099
        have hw : |(220872137/400000000 : ℝ)|=(220872137/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2672442009/10000000000 : ℝ)|^4123 ≤ (17279933685361/100000000000000 : ℝ)^3099
        have hw : |(-2672442009/10000000000 : ℝ)|=(2672442009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2384557393/5000000000 : ℝ)|^4123 ≤ (7468170628407/20000000000000 : ℝ)^3099
        have hw : |(2384557393/5000000000 : ℝ)|=(2384557393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1104360809/2000000000 : ℝ)*x 0 + (2384557597/5000000000 : ℝ)*x 1 + (-2672440727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104360809/2000000000 : ℝ)^4123 ≤ (45379219937749/100000000000000 : ℝ)^3099 := by
    have hnat : (1104360809 : ℕ)^4123*100000000000000^3099 ≤ 45379219937749^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104360809 2000000000 45379219937749 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384557597/5000000000 : ℝ)^4123 ≤ (36465681047/97656250000 : ℝ)^3099 := by
    have hnat : (2384557597 : ℕ)^4123*97656250000^3099 ≤ 36465681047^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384557597 5000000000 36465681047 97656250000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2672440727/10000000000 : ℝ)^4123 ≤ (3455984531387/20000000000000 : ℝ)^3099 := by
    have hnat : (2672440727 : ℕ)^4123*20000000000000^3099 ≤ 3455984531387^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672440727 10000000000 3455984531387 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104360809/2000000000 : ℝ), (2384557597/5000000000 : ℝ), (-2672440727/10000000000 : ℝ)] ![(45379219937749/100000000000000 : ℝ), (36465681047/97656250000 : ℝ), (3455984531387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104360809/2000000000 : ℝ)|^4123 ≤ (45379219937749/100000000000000 : ℝ)^3099
        have hw : |(1104360809/2000000000 : ℝ)|=(1104360809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2384557597/5000000000 : ℝ)|^4123 ≤ (36465681047/97656250000 : ℝ)^3099
        have hw : |(2384557597/5000000000 : ℝ)|=(2384557597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2672440727/10000000000 : ℝ)|^4123 ≤ (3455984531387/20000000000000 : ℝ)^3099
        have hw : |(-2672440727/10000000000 : ℝ)|=(2672440727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208285147/10000000000 : ℝ)*x 0 + (78139251/250000000 : ℝ)*x 1 + (5678575349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208285147/10000000000 : ℝ)^4123 ≤ (15807694827057/50000000000000 : ℝ)^3099 := by
    have hnat : (4208285147 : ℕ)^4123*50000000000000^3099 ≤ 15807694827057^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208285147 10000000000 15807694827057 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78139251/250000000 : ℝ)^4123 ≤ (21283307581939/100000000000000 : ℝ)^3099 := by
    have hnat : (78139251 : ℕ)^4123*100000000000000^3099 ≤ 21283307581939^3099*250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78139251 250000000 21283307581939 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678575349/10000000000 : ℝ)^4123 ≤ (47101302746759/100000000000000 : ℝ)^3099 := by
    have hnat : (5678575349 : ℕ)^4123*100000000000000^3099 ≤ 47101302746759^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678575349 10000000000 47101302746759 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208285147/10000000000 : ℝ), (78139251/250000000 : ℝ), (5678575349/10000000000 : ℝ)] ![(15807694827057/50000000000000 : ℝ), (21283307581939/100000000000000 : ℝ), (47101302746759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208285147/10000000000 : ℝ)|^4123 ≤ (15807694827057/50000000000000 : ℝ)^3099
        have hw : |(4208285147/10000000000 : ℝ)|=(4208285147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78139251/250000000 : ℝ)|^4123 ≤ (21283307581939/100000000000000 : ℝ)^3099
        have hw : |(78139251/250000000 : ℝ)|=(78139251/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678575349/10000000000 : ℝ)|^4123 ≤ (47101302746759/100000000000000 : ℝ)^3099
        have hw : |(5678575349/10000000000 : ℝ)|=(5678575349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-385142791/2000000000 : ℝ)*x 0 + (2401420729/5000000000 : ℝ)*x 1 + (6040224607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385142791/2000000000 : ℝ)^4123 ≤ (5586888914973/50000000000000 : ℝ)^3099 := by
    have hnat : (385142791 : ℕ)^4123*50000000000000^3099 ≤ 5586888914973^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385142791 2000000000 5586888914973 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401420729/5000000000 : ℝ)^4123 ≤ (37692590126181/100000000000000 : ℝ)^3099 := by
    have hnat : (2401420729 : ℕ)^4123*100000000000000^3099 ≤ 37692590126181^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401420729 5000000000 37692590126181 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6040224607/10000000000 : ℝ)^4123 ≤ (51133632023741/100000000000000 : ℝ)^3099 := by
    have hnat : (6040224607 : ℕ)^4123*100000000000000^3099 ≤ 51133632023741^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040224607 10000000000 51133632023741 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385142791/2000000000 : ℝ), (2401420729/5000000000 : ℝ), (6040224607/10000000000 : ℝ)] ![(5586888914973/50000000000000 : ℝ), (37692590126181/100000000000000 : ℝ), (51133632023741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385142791/2000000000 : ℝ)|^4123 ≤ (5586888914973/50000000000000 : ℝ)^3099
        have hw : |(-385142791/2000000000 : ℝ)|=(385142791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401420729/5000000000 : ℝ)|^4123 ≤ (37692590126181/100000000000000 : ℝ)^3099
        have hw : |(2401420729/5000000000 : ℝ)|=(2401420729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6040224607/10000000000 : ℝ)|^4123 ≤ (51133632023741/100000000000000 : ℝ)^3099
        have hw : |(6040224607/10000000000 : ℝ)|=(6040224607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2583701567/5000000000 : ℝ)*x 0 + (-700666451/5000000000 : ℝ)*x 1 + (1510055981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583701567/5000000000 : ℝ)^4123 ≤ (20772997417123/50000000000000 : ℝ)^3099 := by
    have hnat : (2583701567 : ℕ)^4123*50000000000000^3099 ≤ 20772997417123^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583701567 5000000000 20772997417123 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700666451/5000000000 : ℝ)^4123 ≤ (146407616499/2000000000000 : ℝ)^3099 := by
    have hnat : (700666451 : ℕ)^4123*2000000000000^3099 ≤ 146407616499^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700666451 5000000000 146407616499 2000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510055981/2500000000 : ℝ)^4123 ≤ (12783406082817/25000000000000 : ℝ)^3099 := by
    have hnat : (1510055981 : ℕ)^4123*25000000000000^3099 ≤ 12783406082817^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510055981 2500000000 12783406082817 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583701567/5000000000 : ℝ), (-700666451/5000000000 : ℝ), (1510055981/2500000000 : ℝ)] ![(20772997417123/50000000000000 : ℝ), (146407616499/2000000000000 : ℝ), (12783406082817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583701567/5000000000 : ℝ)|^4123 ≤ (20772997417123/50000000000000 : ℝ)^3099
        have hw : |(2583701567/5000000000 : ℝ)|=(2583701567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700666451/5000000000 : ℝ)|^4123 ≤ (146407616499/2000000000000 : ℝ)^3099
        have hw : |(-700666451/5000000000 : ℝ)|=(700666451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510055981/2500000000 : ℝ)|^4123 ≤ (12783406082817/25000000000000 : ℝ)^3099
        have hw : |(1510055981/2500000000 : ℝ)|=(1510055981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1291851131/2500000000 : ℝ)*x 0 + (1510055761/2500000000 : ℝ)*x 1 + (-1401332189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291851131/2500000000 : ℝ)^4123 ≤ (20773004851309/50000000000000 : ℝ)^3099 := by
    have hnat : (1291851131 : ℕ)^4123*50000000000000^3099 ≤ 20773004851309^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291851131 2500000000 20773004851309 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510055761/2500000000 : ℝ)^4123 ≤ (12783403605007/25000000000000 : ℝ)^3099 := by
    have hnat : (1510055761 : ℕ)^4123*25000000000000^3099 ≤ 12783403605007^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510055761 2500000000 12783403605007 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401332189/10000000000 : ℝ)^4123 ≤ (915046983701/12500000000000 : ℝ)^3099 := by
    have hnat : (1401332189 : ℕ)^4123*12500000000000^3099 ≤ 915046983701^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401332189 10000000000 915046983701 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291851131/2500000000 : ℝ), (1510055761/2500000000 : ℝ), (-1401332189/10000000000 : ℝ)] ![(20773004851309/50000000000000 : ℝ), (12783403605007/25000000000000 : ℝ), (915046983701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291851131/2500000000 : ℝ)|^4123 ≤ (20773004851309/50000000000000 : ℝ)^3099
        have hw : |(1291851131/2500000000 : ℝ)|=(1291851131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510055761/2500000000 : ℝ)|^4123 ≤ (12783403605007/25000000000000 : ℝ)^3099
        have hw : |(1510055761/2500000000 : ℝ)|=(1510055761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1401332189/10000000000 : ℝ)|^4123 ≤ (915046983701/12500000000000 : ℝ)^3099
        have hw : |(-1401332189/10000000000 : ℝ)|=(1401332189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s0_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131839661/312500000 : ℝ)*x 0 + (2806320881/5000000000 : ℝ)*x 1 + (798450647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131839661/312500000 : ℝ)^4123 ≤ (15860610643187/50000000000000 : ℝ)^3099 := by
    have hnat : (131839661 : ℕ)^4123*50000000000000^3099 ≤ 15860610643187^3099*312500000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131839661 312500000 15860610643187 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806320881/5000000000 : ℝ)^4123 ≤ (46375103307743/100000000000000 : ℝ)^3099 := by
    have hnat : (2806320881 : ℕ)^4123*100000000000000^3099 ≤ 46375103307743^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806320881 5000000000 46375103307743 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (798450647/2500000000 : ℝ)^4123 ≤ (2190367538871/10000000000000 : ℝ)^3099 := by
    have hnat : (798450647 : ℕ)^4123*10000000000000^3099 ≤ 2190367538871^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798450647 2500000000 2190367538871 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131839661/312500000 : ℝ), (2806320881/5000000000 : ℝ), (798450647/2500000000 : ℝ)] ![(15860610643187/50000000000000 : ℝ), (46375103307743/100000000000000 : ℝ), (2190367538871/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131839661/312500000 : ℝ)|^4123 ≤ (15860610643187/50000000000000 : ℝ)^3099
        have hw : |(131839661/312500000 : ℝ)|=(131839661/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2806320881/5000000000 : ℝ)|^4123 ≤ (46375103307743/100000000000000 : ℝ)^3099
        have hw : |(2806320881/5000000000 : ℝ)|=(2806320881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(798450647/2500000000 : ℝ)|^4123 ≤ (2190367538871/10000000000000 : ℝ)^3099
        have hw : |(798450647/2500000000 : ℝ)|=(798450647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (41/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (176/625 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8245/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8245 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8245*1^2048 ≤ 0^2048*1^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8245/2048 : ℝ) ≤ (1250004905846378027/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8245 ≤ (1250004905846378027/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8245*50000000000000000000^2048 ≤ 1250004905846378027^2048*5^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1250004905846378027 50000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1250004905846378027/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8245 := by
      have hnat : (1 : ℕ)^2048*1^8245 ≤ 1^8245*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51250004905846378027/50000000000000000000 : ℝ) ≤ (2012304686878563/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (51250004905846378027/50000000000000000000 : ℝ)^2048 ≤ (2012304686878563/2000000000000000 : ℝ)^8245 := by
      have hnat : (51250004905846378027 : ℕ)^2048*2000000000000000^8245 ≤ 2012304686878563^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51250004905846378027 50000000000000000000 2012304686878563 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012304686878563/2000000000000000 : ℝ)) (X := (51250004905846378027/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26250004905846378027/25000000000000000000 : ℝ) ≤ (1012304686878563/1000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (26250004905846378027/25000000000000000000 : ℝ)^2048 ≤ (1012304686878563/1000000000000000 : ℝ)^8245 := by
      have hnat : (26250004905846378027 : ℕ)^2048*1000000000000000^8245 ≤ 1012304686878563^8245*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26250004905846378027 25000000000000000000 1012304686878563 1000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012304686878563/1000000000000000 : ℝ)) (X := (26250004905846378027/25000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12304686878563/800000000000000 : ℝ)*(0 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12304686878563/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1250004905846378027/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12304686878563/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (1 : ℝ)+(12304686878563/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012304686878563/2000000000000000 : ℝ) by norm_num, show 1+(1250004905846378027/50000000000000000000 : ℝ)+(0 : ℝ)=(51250004905846378027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1250004905846378027/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12304686878563/800000000000000 : ℝ)*(2/5 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12304686878563/800000000000000 : ℝ)*(2/5 : ℝ)=(1012304686878563/1000000000000000 : ℝ) by norm_num, show 1+2*(1250004905846378027/50000000000000000000 : ℝ)=(26250004905846378027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12304686878563/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12304686878563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12304686878563/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12304686878563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12304686878563/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12304686878563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-480075721/2500000000 : ℝ)*X 0 0+(3037564679/5000000000 : ℝ)*X 0 1+(4769113853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((220872137/400000000 : ℝ)*X 1 0+(-2672442009/10000000000 : ℝ)*X 1 1+(2384557393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104360809/2000000000 : ℝ)*X 2 0+(2384557597/5000000000 : ℝ)*X 2 1+(-2672440727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208285147/10000000000 : ℝ)*X 0 0+(78139251/250000000 : ℝ)*X 0 1+(5678575349/10000000000 : ℝ)*X 0 2+(4208285147/10000000000 : ℝ)*X 1 0+(78139251/250000000 : ℝ)*X 1 1+(5678575349/10000000000 : ℝ)*X 1 2+(4208285147/10000000000 : ℝ)*X 2 0+(78139251/250000000 : ℝ)*X 2 1+(5678575349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-385142791/2000000000 : ℝ)*X 0 0+(2401420729/5000000000 : ℝ)*X 0 1+(6040224607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2583701567/5000000000 : ℝ)*X 1 0+(-700666451/5000000000 : ℝ)*X 1 1+(1510055981/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1291851131/2500000000 : ℝ)*X 2 0+(1510055761/2500000000 : ℝ)*X 2 1+(-1401332189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((131839661/312500000 : ℝ)*X 0 0+(2806320881/5000000000 : ℝ)*X 0 1+(798450647/2500000000 : ℝ)*X 0 2+(131839661/312500000 : ℝ)*X 1 0+(2806320881/5000000000 : ℝ)*X 1 1+(798450647/2500000000 : ℝ)*X 1 2+(131839661/312500000 : ℝ)*X 2 0+(2806320881/5000000000 : ℝ)*X 2 1+(798450647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27852714010996551857679/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (801927799/100000000000000 : ℝ)*(base19) + (352484231/25000000000000 : ℝ)*(base23) + (5269163/2500000000000 : ℝ)*(base24) + (75379857/10000000000000 : ℝ)*(base39) + (420618381/100000000000000 : ℝ)*(upper3) + (115739792888973/20000000000000 : ℝ)*(major0) + (115739792888973/20000000000000 : ℝ)*(major1) + (115739642129259/20000000000000 : ℝ)*(major2) + (382848003479471/50000000000000 : ℝ)*(sp0) + (95711969761671/12500000000000 : ℝ)*(sp1) + (765695693116293/100000000000000 : ℝ)*(sp2) + (391697105489883/100000000000000 : ℝ)*(sp3) + (276531113/50000000000000 : ℝ)*(sp4) + (3277474151/100000000000000 : ℝ)*(sp7) + (78340076592807/20000000000000 : ℝ)*(f.failure) + (382848656909869/50000000000000 : ℝ)*(f.sum) + (8117473980077/2000000000000000000000000000 : ℝ)*base65 + (70782463841183/16000000000000000000000000000 : ℝ)*base68 + (79344742177799/16000000000000000000000000000 : ℝ)*base69 + (33637391726817/16000000000000000000000000000 : ℝ)*base71 + (5550878230077/2000000000000000000000000000 : ℝ)*base73 + (93496413537799/16000000000000000000000000000 : ℝ)*base75 + (2900814222201/16000000000000000000000000000 : ℝ)*base78 + (37107309201799/16000000000000000000000000000 : ℝ)*base79 + (43054337233799/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14076663/2000000000000000000000 : ℝ)*base89 + (14076663/2000000000000000000000 : ℝ)*base91 + (14076663/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112495242597060501347331/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14020521/10000000000000 : ℝ)*(base1) + (606344329/50000000000000 : ℝ)*(base19) + (180547399/12500000000000 : ℝ)*(base23) + (214014627/100000000000000 : ℝ)*(base45) + (12629877/10000000000000 : ℝ)*(upper3) + (222469473/100000000000000 : ℝ)*(upper5) + (610788416030393/100000000000000 : ℝ)*(major0) + (610788416030393/100000000000000 : ℝ)*(major1) + (610788416030393/100000000000000 : ℝ)*(major2) + (20853149/10000000000000 : ℝ)*(sp2) + (808156213512649/100000000000000 : ℝ)*(sp4) + (808154860618781/100000000000000 : ℝ)*(sp5) + (808154420396757/100000000000000 : ℝ)*(sp6) + (20671021552803/5000000000000 : ℝ)*(sp7) + (413420571261269/100000000000000 : ℝ)*(f.failure) + (808156073307439/100000000000000 : ℝ)*(f.sum) + (7259264834741/40000000000000000000000000000 : ℝ)*base66 + (908027888794741/80000000000000000000000000000 : ℝ)*base68 + (256256469674741/80000000000000000000000000000 : ℝ)*base70 + (259351153754741/80000000000000000000000000000 : ℝ)*base72 + (233515302154741/40000000000000000000000000000 : ℝ)*base74 + (899805485754741/80000000000000000000000000000 : ℝ)*base76 + (488946838874741/80000000000000000000000000000 : ℝ)*base78 + (285317898874741/80000000000000000000000000000 : ℝ)*base80 + (125636650914741/40000000000000000000000000000 : ℝ)*base82 + (24334779/10000000000000000000000 : ℝ)*base90 + (24334779/10000000000000000000000 : ℝ)*base92 + (24334779/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1053_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (41/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (176/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s1_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065681737/5000000000 : ℝ)*x 0 + (229039389/400000000 : ℝ)*x 1 + (2491541653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065681737/5000000000 : ℝ)^4123 ≤ (1598587425681/12500000000000 : ℝ)^3099 := by
    have hnat : (1065681737 : ℕ)^4123*12500000000000^3099 ≤ 1598587425681^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065681737 5000000000 1598587425681 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229039389/400000000 : ℝ)^4123 ≤ (23812600555767/50000000000000 : ℝ)^3099 := by
    have hnat : (229039389 : ℕ)^4123*50000000000000^3099 ≤ 23812600555767^3099*400000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229039389 400000000 23812600555767 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491541653/5000000000 : ℝ)^4123 ≤ (19793049728629/50000000000000 : ℝ)^3099 := by
    have hnat : (2491541653 : ℕ)^4123*50000000000000^3099 ≤ 19793049728629^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491541653 5000000000 19793049728629 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065681737/5000000000 : ℝ), (229039389/400000000 : ℝ), (2491541653/5000000000 : ℝ)] ![(1598587425681/12500000000000 : ℝ), (23812600555767/50000000000000 : ℝ), (19793049728629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065681737/5000000000 : ℝ)|^4123 ≤ (1598587425681/12500000000000 : ℝ)^3099
        have hw : |(-1065681737/5000000000 : ℝ)|=(1065681737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229039389/400000000 : ℝ)|^4123 ≤ (23812600555767/50000000000000 : ℝ)^3099
        have hw : |(229039389/400000000 : ℝ)|=(229039389/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491541653/5000000000 : ℝ)|^4123 ≤ (19793049728629/50000000000000 : ℝ)^3099
        have hw : |(2491541653/5000000000 : ℝ)|=(2491541653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2712015619/5000000000 : ℝ)*x 0 + (-101365963/400000000 : ℝ)*x 1 + (311442727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712015619/5000000000 : ℝ)^4123 ≤ (22156669792563/50000000000000 : ℝ)^3099 := by
    have hnat : (2712015619 : ℕ)^4123*50000000000000^3099 ≤ 22156669792563^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712015619 5000000000 22156669792563 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101365963/400000000 : ℝ)^4123 ≤ (2012569686913/12500000000000 : ℝ)^3099 := by
    have hnat : (101365963 : ℕ)^4123*12500000000000^3099 ≤ 2012569686913^3099*400000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101365963 400000000 2012569686913 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311442727/625000000 : ℝ)^4123 ≤ (39586102902771/100000000000000 : ℝ)^3099 := by
    have hnat : (311442727 : ℕ)^4123*100000000000000^3099 ≤ 39586102902771^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311442727 625000000 39586102902771 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712015619/5000000000 : ℝ), (-101365963/400000000 : ℝ), (311442727/625000000 : ℝ)] ![(22156669792563/50000000000000 : ℝ), (2012569686913/12500000000000 : ℝ), (39586102902771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712015619/5000000000 : ℝ)|^4123 ≤ (22156669792563/50000000000000 : ℝ)^3099
        have hw : |(2712015619/5000000000 : ℝ)|=(2712015619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101365963/400000000 : ℝ)|^4123 ≤ (2012569686913/12500000000000 : ℝ)^3099
        have hw : |(-101365963/400000000 : ℝ)|=(101365963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311442727/625000000 : ℝ)|^4123 ≤ (39586102902771/100000000000000 : ℝ)^3099
        have hw : |(311442727/625000000 : ℝ)|=(311442727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5424031699/10000000000 : ℝ)*x 0 + (124577077/250000000 : ℝ)*x 1 + (-633537293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424031699/10000000000 : ℝ)^4123 ≤ (22156672297951/50000000000000 : ℝ)^3099 := by
    have hnat : (5424031699 : ℕ)^4123*50000000000000^3099 ≤ 22156672297951^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424031699 10000000000 22156672297951 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124577077/250000000 : ℝ)^4123 ≤ (39586097068651/100000000000000 : ℝ)^3099 := by
    have hnat : (124577077 : ℕ)^4123*100000000000000^3099 ≤ 39586097068651^3099*250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124577077 250000000 39586097068651 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633537293/2500000000 : ℝ)^4123 ≤ (644022332609/4000000000000 : ℝ)^3099 := by
    have hnat : (633537293 : ℕ)^4123*4000000000000^3099 ≤ 644022332609^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633537293 2500000000 644022332609 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424031699/10000000000 : ℝ), (124577077/250000000 : ℝ), (-633537293/2500000000 : ℝ)] ![(22156672297951/50000000000000 : ℝ), (39586097068651/100000000000000 : ℝ), (644022332609/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424031699/10000000000 : ℝ)|^4123 ≤ (22156672297951/50000000000000 : ℝ)^3099
        have hw : |(5424031699/10000000000 : ℝ)|=(5424031699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124577077/250000000 : ℝ)|^4123 ≤ (39586097068651/100000000000000 : ℝ)^3099
        have hw : |(124577077/250000000 : ℝ)|=(124577077/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-633537293/2500000000 : ℝ)|^4123 ≤ (644022332609/4000000000000 : ℝ)^3099
        have hw : |(-633537293/2500000000 : ℝ)|=(633537293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108121879/250000000 : ℝ)*x 0 + (3660015919/10000000000 : ℝ)*x 1 + (159757543/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108121879/250000000 : ℝ)^4123 ≤ (32786014481353/100000000000000 : ℝ)^3099 := by
    have hnat : (108121879 : ℕ)^4123*100000000000000^3099 ≤ 32786014481353^3099*250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108121879 250000000 32786014481353 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660015919/10000000000 : ℝ)^4123 ≤ (13128497321113/50000000000000 : ℝ)^3099 := by
    have hnat : (3660015919 : ℕ)^4123*50000000000000^3099 ≤ 13128497321113^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660015919 10000000000 13128497321113 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159757543/312500000 : ℝ)^4123 ≤ (40956990871557/100000000000000 : ℝ)^3099 := by
    have hnat : (159757543 : ℕ)^4123*100000000000000^3099 ≤ 40956990871557^3099*312500000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159757543 312500000 40956990871557 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108121879/250000000 : ℝ), (3660015919/10000000000 : ℝ), (159757543/312500000 : ℝ)] ![(32786014481353/100000000000000 : ℝ), (13128497321113/50000000000000 : ℝ), (40956990871557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108121879/250000000 : ℝ)|^4123 ≤ (32786014481353/100000000000000 : ℝ)^3099
        have hw : |(108121879/250000000 : ℝ)|=(108121879/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3660015919/10000000000 : ℝ)|^4123 ≤ (13128497321113/50000000000000 : ℝ)^3099
        have hw : |(3660015919/10000000000 : ℝ)|=(3660015919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159757543/312500000 : ℝ)|^4123 ≤ (40956990871557/100000000000000 : ℝ)^3099
        have hw : |(159757543/312500000 : ℝ)|=(159757543/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066153087/5000000000 : ℝ)*x 0 + (4993574817/10000000000 : ℝ)*x 1 + (2857638579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066153087/5000000000 : ℝ)^4123 ≤ (6398112716967/50000000000000 : ℝ)^3099 := by
    have hnat : (1066153087 : ℕ)^4123*50000000000000^3099 ≤ 6398112716967^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066153087 5000000000 6398112716967 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993574817/10000000000 : ℝ)^4123 ≤ (39697023409081/100000000000000 : ℝ)^3099 := by
    have hnat : (4993574817 : ℕ)^4123*100000000000000^3099 ≤ 39697023409081^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993574817 10000000000 39697023409081 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2857638579/5000000000 : ℝ)^4123 ≤ (47506751144469/100000000000000 : ℝ)^3099 := by
    have hnat : (2857638579 : ℕ)^4123*100000000000000^3099 ≤ 47506751144469^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857638579 5000000000 47506751144469 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066153087/5000000000 : ℝ), (4993574817/10000000000 : ℝ), (2857638579/5000000000 : ℝ)] ![(6398112716967/50000000000000 : ℝ), (39697023409081/100000000000000 : ℝ), (47506751144469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066153087/5000000000 : ℝ)|^4123 ≤ (6398112716967/50000000000000 : ℝ)^3099
        have hw : |(-1066153087/5000000000 : ℝ)|=(1066153087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993574817/10000000000 : ℝ)|^4123 ≤ (39697023409081/100000000000000 : ℝ)^3099
        have hw : |(4993574817/10000000000 : ℝ)|=(4993574817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2857638579/5000000000 : ℝ)|^4123 ≤ (47506751144469/100000000000000 : ℝ)^3099
        have hw : |(2857638579/5000000000 : ℝ)|=(2857638579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1308608937/2500000000 : ℝ)*x 0 + (-112622107/625000000 : ℝ)*x 1 + (5715278553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308608937/2500000000 : ℝ)^4123 ≤ (42264552853763/100000000000000 : ℝ)^3099 := by
    have hnat : (1308608937 : ℕ)^4123*100000000000000^3099 ≤ 42264552853763^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308608937 2500000000 42264552853763 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112622107/625000000 : ℝ)^4123 ≤ (511434028027/5000000000000 : ℝ)^3099 := by
    have hnat : (112622107 : ℕ)^4123*5000000000000^3099 ≤ 511434028027^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112622107 625000000 511434028027 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715278553/10000000000 : ℝ)^4123 ≤ (1187669164289/2500000000000 : ℝ)^3099 := by
    have hnat : (5715278553 : ℕ)^4123*2500000000000^3099 ≤ 1187669164289^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715278553 10000000000 1187669164289 2500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308608937/2500000000 : ℝ), (-112622107/625000000 : ℝ), (5715278553/10000000000 : ℝ)] ![(42264552853763/100000000000000 : ℝ), (511434028027/5000000000000 : ℝ), (1187669164289/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308608937/2500000000 : ℝ)|^4123 ≤ (42264552853763/100000000000000 : ℝ)^3099
        have hw : |(1308608937/2500000000 : ℝ)|=(1308608937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112622107/625000000 : ℝ)|^4123 ≤ (511434028027/5000000000000 : ℝ)^3099
        have hw : |(-112622107/625000000 : ℝ)|=(112622107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5715278553/10000000000 : ℝ)|^4123 ≤ (1187669164289/2500000000000 : ℝ)^3099
        have hw : |(5715278553/10000000000 : ℝ)|=(5715278553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20447007/39062500 : ℝ)*x 0 + (5715280703/10000000000 : ℝ)*x 1 + (-900976673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20447007/39062500 : ℝ)^4123 ≤ (42264531841783/100000000000000 : ℝ)^3099 := by
    have hnat : (20447007 : ℕ)^4123*100000000000000^3099 ≤ 42264531841783^3099*39062500^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20447007 39062500 42264531841783 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5715280703/10000000000 : ℝ)^4123 ≤ (47506790348081/100000000000000 : ℝ)^3099 := by
    have hnat : (5715280703 : ℕ)^4123*100000000000000^3099 ≤ 47506790348081^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715280703 10000000000 47506790348081 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900976673/5000000000 : ℝ)^4123 ≤ (10228677796471/100000000000000 : ℝ)^3099 := by
    have hnat : (900976673 : ℕ)^4123*100000000000000^3099 ≤ 10228677796471^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900976673 5000000000 10228677796471 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20447007/39062500 : ℝ), (5715280703/10000000000 : ℝ), (-900976673/5000000000 : ℝ)] ![(42264531841783/100000000000000 : ℝ), (47506790348081/100000000000000 : ℝ), (10228677796471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20447007/39062500 : ℝ)|^4123 ≤ (42264531841783/100000000000000 : ℝ)^3099
        have hw : |(20447007/39062500 : ℝ)|=(20447007/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5715280703/10000000000 : ℝ)|^4123 ≤ (47506790348081/100000000000000 : ℝ)^3099
        have hw : |(5715280703/10000000000 : ℝ)|=(5715280703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900976673/5000000000 : ℝ)|^4123 ≤ (10228677796471/100000000000000 : ℝ)^3099
        have hw : |(-900976673/5000000000 : ℝ)|=(900976673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081678627/2500000000 : ℝ)*x 0 + (31823307/62500000 : ℝ)*x 1 + (460118023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081678627/2500000000 : ℝ)^4123 ≤ (32804566929449/100000000000000 : ℝ)^3099 := by
    have hnat : (1081678627 : ℕ)^4123*100000000000000^3099 ≤ 32804566929449^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081678627 2500000000 32804566929449 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31823307/62500000 : ℝ)^4123 ≤ (40738499833707/100000000000000 : ℝ)^3099 := by
    have hnat : (31823307 : ℕ)^4123*100000000000000^3099 ≤ 40738499833707^3099*62500000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31823307 62500000 40738499833707 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460118023/1250000000 : ℝ)^4123 ≤ (26456933217247/100000000000000 : ℝ)^3099 := by
    have hnat : (460118023 : ℕ)^4123*100000000000000^3099 ≤ 26456933217247^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460118023 1250000000 26456933217247 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081678627/2500000000 : ℝ), (31823307/62500000 : ℝ), (460118023/1250000000 : ℝ)] ![(32804566929449/100000000000000 : ℝ), (40738499833707/100000000000000 : ℝ), (26456933217247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081678627/2500000000 : ℝ)|^4123 ≤ (32804566929449/100000000000000 : ℝ)^3099
        have hw : |(1081678627/2500000000 : ℝ)|=(1081678627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31823307/62500000 : ℝ)|^4123 ≤ (40738499833707/100000000000000 : ℝ)^3099
        have hw : |(31823307/62500000 : ℝ)|=(31823307/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460118023/1250000000 : ℝ)|^4123 ≤ (26456933217247/100000000000000 : ℝ)^3099
        have hw : |(460118023/1250000000 : ℝ)|=(460118023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_8 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (462367/500000000 : ℝ)*x 0 + (171555713/312500000 : ℝ)*x 1 + (3188508273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462367/500000000 : ℝ)^4123 ≤ (919391071/10000000000000 : ℝ)^3099 := by
    have hnat : (462367 : ℕ)^4123*10000000000000^3099 ≤ 919391071^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462367 500000000 919391071 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171555713/312500000 : ℝ)^4123 ≤ (45029444782131/100000000000000 : ℝ)^3099 := by
    have hnat : (171555713 : ℕ)^4123*100000000000000^3099 ≤ 45029444782131^3099*312500000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171555713 312500000 45029444782131 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188508273/5000000000 : ℝ)^4123 ≤ (27480680645783/50000000000000 : ℝ)^3099 := by
    have hnat : (3188508273 : ℕ)^4123*50000000000000^3099 ≤ 27480680645783^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188508273 5000000000 27480680645783 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(462367/500000000 : ℝ), (171555713/312500000 : ℝ), (3188508273/5000000000 : ℝ)] ![(919391071/10000000000000 : ℝ), (45029444782131/100000000000000 : ℝ), (27480680645783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(462367/500000000 : ℝ)|^4123 ≤ (919391071/10000000000000 : ℝ)^3099
        have hw : |(462367/500000000 : ℝ)|=(462367/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171555713/312500000 : ℝ)|^4123 ≤ (45029444782131/100000000000000 : ℝ)^3099
        have hw : |(171555713/312500000 : ℝ)|=(171555713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188508273/5000000000 : ℝ)|^4123 ≤ (27480680645783/50000000000000 : ℝ)^3099
        have hw : |(3188508273/5000000000 : ℝ)|=(3188508273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_9 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (240295549/2500000000 : ℝ)*x 0 + (-4467493067/10000000000 : ℝ)*x 1 + (432825491/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240295549/2500000000 : ℝ)^4123 ≤ (4432972678439/100000000000000 : ℝ)^3099 := by
    have hnat : (240295549 : ℕ)^4123*100000000000000^3099 ≤ 4432972678439^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240295549 2500000000 4432972678439 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4467493067/10000000000 : ℝ)^4123 ≤ (8558049543421/25000000000000 : ℝ)^3099 := by
    have hnat : (4467493067 : ℕ)^4123*25000000000000^3099 ≤ 8558049543421^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467493067 10000000000 8558049543421 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432825491/625000000 : ℝ)^4123 ≤ (7666853641769/12500000000000 : ℝ)^3099 := by
    have hnat : (432825491 : ℕ)^4123*12500000000000^3099 ≤ 7666853641769^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432825491 625000000 7666853641769 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(240295549/2500000000 : ℝ), (-4467493067/10000000000 : ℝ), (432825491/625000000 : ℝ)] ![(4432972678439/100000000000000 : ℝ), (8558049543421/25000000000000 : ℝ), (7666853641769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(240295549/2500000000 : ℝ)|^4123 ≤ (4432972678439/100000000000000 : ℝ)^3099
        have hw : |(240295549/2500000000 : ℝ)|=(240295549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4467493067/10000000000 : ℝ)|^4123 ≤ (8558049543421/25000000000000 : ℝ)^3099
        have hw : |(-4467493067/10000000000 : ℝ)|=(4467493067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432825491/625000000 : ℝ)|^4123 ≤ (7666853641769/12500000000000 : ℝ)^3099
        have hw : |(432825491/625000000 : ℝ)|=(432825491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_10 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (961176559/10000000000 : ℝ)*x 0 + (1731298947/2500000000 : ℝ)*x 1 + (-4467510409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961176559/10000000000 : ℝ)^4123 ≤ (221646904509/5000000000000 : ℝ)^3099 := by
    have hnat : (961176559 : ℕ)^4123*5000000000000^3099 ≤ 221646904509^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961176559 10000000000 221646904509 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1731298947/2500000000 : ℝ)^4123 ≤ (76668358667/125000000000 : ℝ)^3099 := by
    have hnat : (1731298947 : ℕ)^4123*125000000000^3099 ≤ 76668358667^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731298947 2500000000 76668358667 125000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4467510409/10000000000 : ℝ)^4123 ≤ (6846474993097/20000000000000 : ℝ)^3099 := by
    have hnat : (4467510409 : ℕ)^4123*20000000000000^3099 ≤ 6846474993097^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467510409 10000000000 6846474993097 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(961176559/10000000000 : ℝ), (1731298947/2500000000 : ℝ), (-4467510409/10000000000 : ℝ)] ![(221646904509/5000000000000 : ℝ), (76668358667/125000000000 : ℝ), (6846474993097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(961176559/10000000000 : ℝ)|^4123 ≤ (221646904509/5000000000000 : ℝ)^3099
        have hw : |(961176559/10000000000 : ℝ)|=(961176559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1731298947/2500000000 : ℝ)|^4123 ≤ (76668358667/125000000000 : ℝ)^3099
        have hw : |(1731298947/2500000000 : ℝ)|=(1731298947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4467510409/10000000000 : ℝ)|^4123 ≤ (6846474993097/20000000000000 : ℝ)^3099
        have hw : |(-4467510409/10000000000 : ℝ)|=(4467510409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s1_11 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1926701013/10000000000 : ℝ)*x 0 + (2916828261/5000000000 : ℝ)*x 1 + (2511014627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926701013/10000000000 : ℝ)^4123 ≤ (5590699129793/50000000000000 : ℝ)^3099 := by
    have hnat : (1926701013 : ℕ)^4123*50000000000000^3099 ≤ 5590699129793^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926701013 10000000000 5590699129793 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2916828261/5000000000 : ℝ)^4123 ≤ (24410174832247/50000000000000 : ℝ)^3099 := by
    have hnat : (2916828261 : ℕ)^4123*50000000000000^3099 ≤ 24410174832247^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916828261 5000000000 24410174832247 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511014627/5000000000 : ℝ)^4123 ≤ (1999912603251/5000000000000 : ℝ)^3099 := by
    have hnat : (2511014627 : ℕ)^4123*5000000000000^3099 ≤ 1999912603251^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511014627 5000000000 1999912603251 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1926701013/10000000000 : ℝ), (2916828261/5000000000 : ℝ), (2511014627/5000000000 : ℝ)] ![(5590699129793/50000000000000 : ℝ), (24410174832247/50000000000000 : ℝ), (1999912603251/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1926701013/10000000000 : ℝ)|^4123 ≤ (5590699129793/50000000000000 : ℝ)^3099
        have hw : |(1926701013/10000000000 : ℝ)|=(1926701013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2916828261/5000000000 : ℝ)|^4123 ≤ (24410174832247/50000000000000 : ℝ)^3099
        have hw : |(2916828261/5000000000 : ℝ)|=(2916828261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511014627/5000000000 : ℝ)|^4123 ≤ (1999912603251/5000000000000 : ℝ)^3099
        have hw : |(2511014627/5000000000 : ℝ)|=(2511014627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (176/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (321/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20853/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (176/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (41/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (176/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (41/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (176/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (41/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (176/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (41/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (176/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (41/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (176/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (41/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (41/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (288661/12500000000000000000 : ℝ) := by
    have hpowers : (41/100000 : ℝ)^8245 ≤ (288661/12500000000000000000 : ℝ)^2048 := by
      have hnat : (41 : ℕ)^8245*12500000000000000000^2048 ≤ 288661^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41 100000 288661 12500000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41/100000 : ℝ)) (X := (288661/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (176/625 : ℝ) ^ (8245/2048 : ℝ) ≤ (38033624476112783/6250000000000000000 : ℝ) := by
    have hpowers : (176/625 : ℝ)^8245 ≤ (38033624476112783/6250000000000000000 : ℝ)^2048 := by
      have hnat : (176 : ℕ)^8245*6250000000000000000^2048 ≤ 38033624476112783^2048*625^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        176 625 38033624476112783 6250000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (176/625 : ℝ)) (X := (38033624476112783/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000000000288661/6250000000000000000 : ℝ) ≤ (2000000000000023/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (6250000000000288661/6250000000000000000 : ℝ)^2048 ≤ (2000000000000023/2000000000000000 : ℝ)^8245 := by
      have hnat : (6250000000000288661 : ℕ)^2048*2000000000000000^8245 ≤ 2000000000000023^8245*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000000000288661 6250000000000000000 2000000000000023 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000000023/2000000000000000 : ℝ)) (X := (6250000000000288661/6250000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12576067248952514227/12500000000000000000 : ℝ) ≤ (10015081209841297/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (12576067248952514227/12500000000000000000 : ℝ)^2048 ≤ (10015081209841297/10000000000000000 : ℝ)^8245 := by
      have hnat : (12576067248952514227 : ℕ)^2048*10000000000000000^8245 ≤ 10015081209841297^8245*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12576067248952514227 12500000000000000000 10015081209841297 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015081209841297/10000000000000000 : ℝ)) (X := (12576067248952514227/12500000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3163033624476112783/3125000000000000000 : ℝ) ≤ (10030162419682479/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (3163033624476112783/3125000000000000000 : ℝ)^2048 ≤ (10030162419682479/10000000000000000 : ℝ)^8245 := by
      have hnat : (3163033624476112783 : ℕ)^2048*10000000000000000^8245 ≤ 10030162419682479^8245*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163033624476112783 3125000000000000000 10030162419682479 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030162419682479/10000000000000000 : ℝ)) (X := (3163033624476112783/3125000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(288661/12500000000000000000 : ℝ) ≤ ((281188763340796256761/281190000000000000000 : ℝ)+2*(7540604920591/1405950000000000 : ℝ)*(41/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (281188763340796256761/281190000000000000000 : ℝ)+2*(7540604920591/1405950000000000 : ℝ)*(41/100000 : ℝ)=(2000000000000023/2000000000000000 : ℝ) by norm_num, show 1+2*(288661/12500000000000000000 : ℝ)=(6250000000000288661/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38033624476112783/6250000000000000000 : ℝ)+(288661/12500000000000000000 : ℝ) ≤ ((281188763340796256761/281190000000000000000 : ℝ)+(7540604920591/1405950000000000 : ℝ)*((176/625 : ℝ)+(41/100000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (281188763340796256761/281190000000000000000 : ℝ)+(7540604920591/1405950000000000 : ℝ)*((176/625 : ℝ)+(41/100000 : ℝ))=(10015081209841297/10000000000000000 : ℝ) by norm_num, show 1+(38033624476112783/6250000000000000000 : ℝ)+(288661/12500000000000000000 : ℝ)=(12576067248952514227/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38033624476112783/6250000000000000000 : ℝ) ≤ ((281188763340796256761/281190000000000000000 : ℝ)+2*(7540604920591/1405950000000000 : ℝ)*(176/625 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (281188763340796256761/281190000000000000000 : ℝ)+2*(7540604920591/1405950000000000 : ℝ)*(176/625 : ℝ)=(10030162419682479/10000000000000000 : ℝ) by norm_num, show 1+2*(38033624476112783/6250000000000000000 : ℝ)=(3163033624476112783/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281188763340796256761/281190000000000000000 : ℝ)*(X 1 0+X 2 0)+(7540604920591/1405950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (41/100000 : ℝ)) (hi := (176/625 : ℝ)) (c := (281188763340796256761/281190000000000000000 : ℝ)) (alpha := (7540604920591/1405950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281188763340796256761/281190000000000000000 : ℝ)*(X 0 1+X 2 1)+(7540604920591/1405950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (41/100000 : ℝ)) (hi := (176/625 : ℝ)) (c := (281188763340796256761/281190000000000000000 : ℝ)) (alpha := (7540604920591/1405950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281188763340796256761/281190000000000000000 : ℝ)*(X 0 2+X 1 2)+(7540604920591/1405950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (41/100000 : ℝ)) (hi := (176/625 : ℝ)) (c := (281188763340796256761/281190000000000000000 : ℝ)) (alpha := (7540604920591/1405950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065681737/5000000000 : ℝ)*X 0 0+(229039389/400000000 : ℝ)*X 0 1+(2491541653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2712015619/5000000000 : ℝ)*X 1 0+(-101365963/400000000 : ℝ)*X 1 1+(311442727/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5424031699/10000000000 : ℝ)*X 2 0+(124577077/250000000 : ℝ)*X 2 1+(-633537293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108121879/250000000 : ℝ)*X 0 0+(3660015919/10000000000 : ℝ)*X 0 1+(159757543/312500000 : ℝ)*X 0 2+(108121879/250000000 : ℝ)*X 1 0+(3660015919/10000000000 : ℝ)*X 1 1+(159757543/312500000 : ℝ)*X 1 2+(108121879/250000000 : ℝ)*X 2 0+(3660015919/10000000000 : ℝ)*X 2 1+(159757543/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1066153087/5000000000 : ℝ)*X 0 0+(4993574817/10000000000 : ℝ)*X 0 1+(2857638579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1308608937/2500000000 : ℝ)*X 1 0+(-112622107/625000000 : ℝ)*X 1 1+(5715278553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20447007/39062500 : ℝ)*X 2 0+(5715280703/10000000000 : ℝ)*X 2 1+(-900976673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081678627/2500000000 : ℝ)*X 0 0+(31823307/62500000 : ℝ)*X 0 1+(460118023/1250000000 : ℝ)*X 0 2+(1081678627/2500000000 : ℝ)*X 1 0+(31823307/62500000 : ℝ)*X 1 1+(460118023/1250000000 : ℝ)*X 1 2+(1081678627/2500000000 : ℝ)*X 2 0+(31823307/62500000 : ℝ)*X 2 1+(460118023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((462367/500000000 : ℝ)*X 0 0+(171555713/312500000 : ℝ)*X 0 1+(3188508273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((240295549/2500000000 : ℝ)*X 1 0+(-4467493067/10000000000 : ℝ)*X 1 1+(432825491/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((961176559/10000000000 : ℝ)*X 2 0+(1731298947/2500000000 : ℝ)*X 2 1+(-4467510409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1926701013/10000000000 : ℝ)*X 0 0+(2916828261/5000000000 : ℝ)*X 0 1+(2511014627/5000000000 : ℝ)*X 0 2+(1926701013/10000000000 : ℝ)*X 1 0+(2916828261/5000000000 : ℝ)*X 1 1+(2511014627/5000000000 : ℝ)*X 1 2+(1926701013/10000000000 : ℝ)*X 2 0+(2916828261/5000000000 : ℝ)*X 2 1+(2511014627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (445906489691030766760579037/36050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101734000081493/10000000000000 : ℝ)*(major0) + (101734000081493/10000000000000 : ℝ)*(major1) + (101734000081493/10000000000000 : ℝ)*(major2) + (1346076326200369/100000000000000 : ℝ)*(sp0) + (673038573008029/50000000000000 : ℝ)*(sp1) + (134607643638963/10000000000000 : ℝ)*(sp2) + (344299551819459/50000000000000 : ℝ)*(sp3) + (1468040423/100000000000000 : ℝ)*(sp4) + (1045464939/100000000000000 : ℝ)*(sp5) + (164136279/10000000000000 : ℝ)*(sp6) + (234251987/20000000000000 : ℝ)*(sp8) + (774019729/100000000000000 : ℝ)*(sp9) + (221937077/25000000000000 : ℝ)*(sp10) + (380046617/25000000000000 : ℝ)*(sp11) + (344300311912693/50000000000000 : ℝ)*(f.failure) + (1346078965500727/100000000000000 : ℝ)*(f.sum) + (76907086559/33796875000000000000000000 : ℝ)*base65 + (50893627425854301/10300000000000000000000000000000 : ℝ)*base67 + (70823712500654301/10300000000000000000000000000000 : ℝ)*base69 + (121503989822854301/10300000000000000000000000000000 : ℝ)*base71 + (5996581892047/2163000000000000000000000000 : ℝ)*base74 + (138293608203954301/10300000000000000000000000000000 : ℝ)*base75 + (35062381454254301/10300000000000000000000000000000 : ℝ)*base77 + (7953335326454301/10300000000000000000000000000000 : ℝ)*base79 + (501867908491/108150000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (46427163/5000000000000000000000 : ℝ)*base90 + (46427163/5000000000000000000000 : ℝ)*base92 + (46427163/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76612175151726501982519373/16737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37356159/25000000000000 : ℝ)*(lower4) + (26180494937149/2500000000000 : ℝ)*(major0) + (26180494937149/2500000000000 : ℝ)*(major1) + (26180494937149/2500000000000 : ℝ)*(major2) + (105180003/6250000000000 : ℝ)*(sp0) + (1868885991/100000000000000 : ℝ)*(sp1) + (4419480747/100000000000000 : ℝ)*(sp2) + (692804777134341/50000000000000 : ℝ)*(sp4) + (1385612225423253/100000000000000 : ℝ)*(sp5) + (69280492311279/5000000000000 : ℝ)*(sp6) + (35441193320297/5000000000000 : ℝ)*(sp7) + (3028557597/100000000000000 : ℝ)*(sp8) + (42849271/25000000000000 : ℝ)*(sp9) + (262056749/20000000000000 : ℝ)*(sp11) + (141765035337937/20000000000000 : ℝ)*(f.failure) + (173201783213291/12500000000000 : ℝ)*(f.sum) + (1545447481013/4017000000000000000000000000 : ℝ)*base66 + (4308379722293093/2575000000000000000000000000000 : ℝ)*base67 + (4004362965293093/2575000000000000000000000000000 : ℝ)*base69 + (15369136660331907/2575000000000000000000000000000 : ℝ)*base72 + (444665732791/160680000000000000000000000 : ℝ)*base73 + (6952879311131907/2575000000000000000000000000000 : ℝ)*base76 + (1395022451143093/2575000000000000000000000000000 : ℝ)*base77 + (4047423160743093/2575000000000000000000000000000 : ℝ)*base79 + (55461115609/80340000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1991167/2000000000000000000000 : ℝ)*base90 + (1991167/2000000000000000000000 : ℝ)*base92 + (1991167/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1053_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (176/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (321/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_s2_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136845243/625000000 : ℝ)*x 0 + (5528613971/10000000000 : ℝ)*x 1 + (5143568527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136845243/625000000 : ℝ)^4123 ≤ (13255068674103/100000000000000 : ℝ)^3099 := by
    have hnat : (136845243 : ℕ)^4123*100000000000000^3099 ≤ 13255068674103^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136845243 625000000 13255068674103 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528613971/10000000000 : ℝ)^4123 ≤ (45453692902521/100000000000000 : ℝ)^3099 := by
    have hnat : (5528613971 : ℕ)^4123*100000000000000^3099 ≤ 45453692902521^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528613971 10000000000 45453692902521 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143568527/10000000000 : ℝ)^4123 ≤ (2580702400419/6250000000000 : ℝ)^3099 := by
    have hnat : (5143568527 : ℕ)^4123*6250000000000^3099 ≤ 2580702400419^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143568527 10000000000 2580702400419 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136845243/625000000 : ℝ), (5528613971/10000000000 : ℝ), (5143568527/10000000000 : ℝ)] ![(13255068674103/100000000000000 : ℝ), (45453692902521/100000000000000 : ℝ), (2580702400419/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136845243/625000000 : ℝ)|^4123 ≤ (13255068674103/100000000000000 : ℝ)^3099
        have hw : |(-136845243/625000000 : ℝ)|=(136845243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528613971/10000000000 : ℝ)|^4123 ≤ (45453692902521/100000000000000 : ℝ)^3099
        have hw : |(5528613971/10000000000 : ℝ)|=(5528613971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143568527/10000000000 : ℝ)|^4123 ≤ (2580702400419/6250000000000 : ℝ)^3099
        have hw : |(5143568527/10000000000 : ℝ)|=(5143568527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377786813/10000000000 : ℝ)*x 0 + (-597610081/2500000000 : ℝ)*x 1 + (5143569931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377786813/10000000000 : ℝ)^4123 ≤ (8762280312387/20000000000000 : ℝ)^3099 := by
    have hnat : (5377786813 : ℕ)^4123*20000000000000^3099 ≤ 8762280312387^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377786813 10000000000 8762280312387 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597610081/2500000000 : ℝ)^4123 ≤ (7448672512911/50000000000000 : ℝ)^3099 := by
    have hnat : (597610081 : ℕ)^4123*50000000000000^3099 ≤ 7448672512911^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597610081 2500000000 7448672512911 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143569931/10000000000 : ℝ)^4123 ≤ (2580703337619/6250000000000 : ℝ)^3099 := by
    have hnat : (5143569931 : ℕ)^4123*6250000000000^3099 ≤ 2580703337619^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143569931 10000000000 2580703337619 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377786813/10000000000 : ℝ), (-597610081/2500000000 : ℝ), (5143569931/10000000000 : ℝ)] ![(8762280312387/20000000000000 : ℝ), (7448672512911/50000000000000 : ℝ), (2580703337619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377786813/10000000000 : ℝ)|^4123 ≤ (8762280312387/20000000000000 : ℝ)^3099
        have hw : |(5377786813/10000000000 : ℝ)|=(5377786813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-597610081/2500000000 : ℝ)|^4123 ≤ (7448672512911/50000000000000 : ℝ)^3099
        have hw : |(-597610081/2500000000 : ℝ)|=(597610081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143569931/10000000000 : ℝ)|^4123 ≤ (2580703337619/6250000000000 : ℝ)^3099
        have hw : |(5143569931/10000000000 : ℝ)|=(5143569931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688893561/5000000000 : ℝ)*x 0 + (2571784677/5000000000 : ℝ)*x 1 + (-1195220331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688893561/5000000000 : ℝ)^4123 ≤ (43811404911079/100000000000000 : ℝ)^3099 := by
    have hnat : (2688893561 : ℕ)^4123*100000000000000^3099 ≤ 43811404911079^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688893561 5000000000 43811404911079 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571784677/5000000000 : ℝ)^4123 ≤ (20645623619673/50000000000000 : ℝ)^3099 := by
    have hnat : (2571784677 : ℕ)^4123*50000000000000^3099 ≤ 20645623619673^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571784677 5000000000 20645623619673 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195220331/5000000000 : ℝ)^4123 ≤ (14897347828283/100000000000000 : ℝ)^3099 := by
    have hnat : (1195220331 : ℕ)^4123*100000000000000^3099 ≤ 14897347828283^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195220331 5000000000 14897347828283 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688893561/5000000000 : ℝ), (2571784677/5000000000 : ℝ), (-1195220331/5000000000 : ℝ)] ![(43811404911079/100000000000000 : ℝ), (20645623619673/50000000000000 : ℝ), (14897347828283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688893561/5000000000 : ℝ)|^4123 ≤ (43811404911079/100000000000000 : ℝ)^3099
        have hw : |(2688893561/5000000000 : ℝ)|=(2688893561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571784677/5000000000 : ℝ)|^4123 ≤ (20645623619673/50000000000000 : ℝ)^3099
        have hw : |(2571784677/5000000000 : ℝ)|=(2571784677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1195220331/5000000000 : ℝ)|^4123 ≤ (14897347828283/100000000000000 : ℝ)^3099
        have hw : |(-1195220331/5000000000 : ℝ)|=(1195220331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182261417/5000000000 : ℝ)*x 0 + (400459219/1000000000 : ℝ)*x 1 + (4757275749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182261417/5000000000 : ℝ)^4123 ≤ (33186494138757/100000000000000 : ℝ)^3099 := by
    have hnat : (2182261417 : ℕ)^4123*100000000000000^3099 ≤ 33186494138757^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182261417 5000000000 33186494138757 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400459219/1000000000 : ℝ)^4123 ≤ (5919185617483/20000000000000 : ℝ)^3099 := by
    have hnat : (400459219 : ℕ)^4123*20000000000000^3099 ≤ 5919185617483^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400459219 1000000000 5919185617483 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4757275749/10000000000 : ℝ)^4123 ≤ (37217577764169/100000000000000 : ℝ)^3099 := by
    have hnat : (4757275749 : ℕ)^4123*100000000000000^3099 ≤ 37217577764169^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4757275749 10000000000 37217577764169 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182261417/5000000000 : ℝ), (400459219/1000000000 : ℝ), (4757275749/10000000000 : ℝ)] ![(33186494138757/100000000000000 : ℝ), (5919185617483/20000000000000 : ℝ), (37217577764169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182261417/5000000000 : ℝ)|^4123 ≤ (33186494138757/100000000000000 : ℝ)^3099
        have hw : |(2182261417/5000000000 : ℝ)|=(2182261417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400459219/1000000000 : ℝ)|^4123 ≤ (5919185617483/20000000000000 : ℝ)^3099
        have hw : |(400459219/1000000000 : ℝ)|=(400459219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4757275749/10000000000 : ℝ)|^4123 ≤ (37217577764169/100000000000000 : ℝ)^3099
        have hw : |(4757275749/10000000000 : ℝ)|=(4757275749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094827053/5000000000 : ℝ)*x 0 + (514639619/1000000000 : ℝ)*x 1 + (5525756579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094827053/5000000000 : ℝ)^4123 ≤ (13256117490193/100000000000000 : ℝ)^3099 := by
    have hnat : (1094827053 : ℕ)^4123*100000000000000^3099 ≤ 13256117490193^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094827053 5000000000 13256117490193 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514639619/1000000000 : ℝ)^4123 ≤ (8264288311133/20000000000000 : ℝ)^3099 := by
    have hnat : (514639619 : ℕ)^4123*20000000000000^3099 ≤ 8264288311133^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514639619 1000000000 8264288311133 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525756579/10000000000 : ℝ)^4123 ≤ (908448818649/2000000000000 : ℝ)^3099 := by
    have hnat : (5525756579 : ℕ)^4123*2000000000000^3099 ≤ 908448818649^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525756579 10000000000 908448818649 2000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094827053/5000000000 : ℝ), (514639619/1000000000 : ℝ), (5525756579/10000000000 : ℝ)] ![(13256117490193/100000000000000 : ℝ), (8264288311133/20000000000000 : ℝ), (908448818649/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094827053/5000000000 : ℝ)|^4123 ≤ (13256117490193/100000000000000 : ℝ)^3099
        have hw : |(-1094827053/5000000000 : ℝ)|=(1094827053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514639619/1000000000 : ℝ)|^4123 ≤ (8264288311133/20000000000000 : ℝ)^3099
        have hw : |(514639619/1000000000 : ℝ)|=(514639619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525756579/10000000000 : ℝ)|^4123 ≤ (908448818649/2000000000000 : ℝ)^3099
        have hw : |(5525756579/10000000000 : ℝ)|=(5525756579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280687279/10000000000 : ℝ)*x 0 + (-2008254167/10000000000 : ℝ)*x 1 + (5525756651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280687279/10000000000 : ℝ)^4123 ≤ (21381062791891/50000000000000 : ℝ)^3099 := by
    have hnat : (5280687279 : ℕ)^4123*50000000000000^3099 ≤ 21381062791891^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280687279 10000000000 21381062791891 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008254167/10000000000 : ℝ)^4123 ≤ (184616135721/1562500000000 : ℝ)^3099 := by
    have hnat : (2008254167 : ℕ)^4123*1562500000000^3099 ≤ 184616135721^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008254167 10000000000 184616135721 1562500000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525756651/10000000000 : ℝ)^4123 ≤ (5677805214983/12500000000000 : ℝ)^3099 := by
    have hnat : (5525756651 : ℕ)^4123*12500000000000^3099 ≤ 5677805214983^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525756651 10000000000 5677805214983 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280687279/10000000000 : ℝ), (-2008254167/10000000000 : ℝ), (5525756651/10000000000 : ℝ)] ![(21381062791891/50000000000000 : ℝ), (184616135721/1562500000000 : ℝ), (5677805214983/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280687279/10000000000 : ℝ)|^4123 ≤ (21381062791891/50000000000000 : ℝ)^3099
        have hw : |(5280687279/10000000000 : ℝ)|=(5280687279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008254167/10000000000 : ℝ)|^4123 ≤ (184616135721/1562500000000 : ℝ)^3099
        have hw : |(-2008254167/10000000000 : ℝ)|=(2008254167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525756651/10000000000 : ℝ)|^4123 ≤ (5677805214983/12500000000000 : ℝ)^3099
        have hw : |(5525756651/10000000000 : ℝ)|=(5525756651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640343757/5000000000 : ℝ)*x 0 + (690719561/1250000000 : ℝ)*x 1 + (-2008254071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640343757/5000000000 : ℝ)^4123 ≤ (5345266014447/12500000000000 : ℝ)^3099 := by
    have hnat : (2640343757 : ℕ)^4123*12500000000000^3099 ≤ 5345266014447^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640343757 5000000000 5345266014447 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690719561/1250000000 : ℝ)^4123 ≤ (45422439937247/100000000000000 : ℝ)^3099 := by
    have hnat : (690719561 : ℕ)^4123*100000000000000^3099 ≤ 45422439937247^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690719561 1250000000 45422439937247 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008254071/10000000000 : ℝ)^4123 ≤ (2363086386941/20000000000000 : ℝ)^3099 := by
    have hnat : (2008254071 : ℕ)^4123*20000000000000^3099 ≤ 2363086386941^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008254071 10000000000 2363086386941 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640343757/5000000000 : ℝ), (690719561/1250000000 : ℝ), (-2008254071/10000000000 : ℝ)] ![(5345266014447/12500000000000 : ℝ), (45422439937247/100000000000000 : ℝ), (2363086386941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640343757/5000000000 : ℝ)|^4123 ≤ (5345266014447/12500000000000 : ℝ)^3099
        have hw : |(2640343757/5000000000 : ℝ)|=(2640343757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690719561/1250000000 : ℝ)|^4123 ≤ (45422439937247/100000000000000 : ℝ)^3099
        have hw : |(690719561/1250000000 : ℝ)|=(690719561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008254071/10000000000 : ℝ)|^4123 ≤ (2363086386941/20000000000000 : ℝ)^3099
        have hw : |(-2008254071/10000000000 : ℝ)|=(2008254071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182388729/5000000000 : ℝ)*x 0 + (4751751279/10000000000 : ℝ)*x 1 + (4010175801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182388729/5000000000 : ℝ)^4123 ≤ (8297267496177/25000000000000 : ℝ)^3099 := by
    have hnat : (2182388729 : ℕ)^4123*25000000000000^3099 ≤ 8297267496177^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182388729 5000000000 8297267496177 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4751751279/10000000000 : ℝ)^4123 ≤ (37160088228029/100000000000000 : ℝ)^3099 := by
    have hnat : (4751751279 : ℕ)^4123*100000000000000^3099 ≤ 37160088228029^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4751751279 10000000000 37160088228029 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010175801/10000000000 : ℝ)^4123 ≤ (7412710442881/25000000000000 : ℝ)^3099 := by
    have hnat : (4010175801 : ℕ)^4123*25000000000000^3099 ≤ 7412710442881^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010175801 10000000000 7412710442881 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182388729/5000000000 : ℝ), (4751751279/10000000000 : ℝ), (4010175801/10000000000 : ℝ)] ![(8297267496177/25000000000000 : ℝ), (37160088228029/100000000000000 : ℝ), (7412710442881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182388729/5000000000 : ℝ)|^4123 ≤ (8297267496177/25000000000000 : ℝ)^3099
        have hw : |(2182388729/5000000000 : ℝ)|=(2182388729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4751751279/10000000000 : ℝ)|^4123 ≤ (37160088228029/100000000000000 : ℝ)^3099
        have hw : |(4751751279/10000000000 : ℝ)|=(4751751279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4010175801/10000000000 : ℝ)|^4123 ≤ (7412710442881/25000000000000 : ℝ)^3099
        have hw : |(4010175801/10000000000 : ℝ)|=(4010175801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_8 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (73/1000000000 : ℝ)*x 0 + (742322109/1250000000 : ℝ)*x 1 + (1485001721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73/1000000000 : ℝ)^4123 ≤ (32001/100000000000000 : ℝ)^3099 := by
    have hnat : (73 : ℕ)^4123*100000000000000^3099 ≤ 32001^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73 1000000000 32001 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742322109/1250000000 : ℝ)^4123 ≤ (2499599587191/5000000000000 : ℝ)^3099 := by
    have hnat : (742322109 : ℕ)^4123*5000000000000^3099 ≤ 2499599587191^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742322109 1250000000 2499599587191 5000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1485001721/2500000000 : ℝ)^4123 ≤ (25004004106353/50000000000000 : ℝ)^3099 := by
    have hnat : (1485001721 : ℕ)^4123*50000000000000^3099 ≤ 25004004106353^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485001721 2500000000 25004004106353 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(73/1000000000 : ℝ), (742322109/1250000000 : ℝ), (1485001721/2500000000 : ℝ)] ![(32001/100000000000000 : ℝ), (2499599587191/5000000000000 : ℝ), (25004004106353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(73/1000000000 : ℝ)|^4123 ≤ (32001/100000000000000 : ℝ)^3099
        have hw : |(73/1000000000 : ℝ)|=(73/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742322109/1250000000 : ℝ)|^4123 ≤ (2499599587191/5000000000000 : ℝ)^3099
        have hw : |(742322109/1250000000 : ℝ)|=(742322109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1485001721/2500000000 : ℝ)|^4123 ≤ (25004004106353/50000000000000 : ℝ)^3099
        have hw : |(1485001721/2500000000 : ℝ)|=(1485001721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_9 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (394261359/5000000000 : ℝ)*x 0 + (-4988132629/10000000000 : ℝ)*x 1 + (6550039561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394261359/5000000000 : ℝ)^4123 ≤ (3406351374391/100000000000000 : ℝ)^3099 := by
    have hnat : (394261359 : ℕ)^4123*100000000000000^3099 ≤ 3406351374391^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394261359 5000000000 3406351374391 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988132629/10000000000 : ℝ)^4123 ≤ (39639474982087/100000000000000 : ℝ)^3099 := by
    have hnat : (4988132629 : ℕ)^4123*100000000000000^3099 ≤ 39639474982087^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988132629 10000000000 39639474982087 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6550039561/10000000000 : ℝ)^4123 ≤ (28477086817949/50000000000000 : ℝ)^3099 := by
    have hnat : (6550039561 : ℕ)^4123*50000000000000^3099 ≤ 28477086817949^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6550039561 10000000000 28477086817949 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(394261359/5000000000 : ℝ), (-4988132629/10000000000 : ℝ), (6550039561/10000000000 : ℝ)] ![(3406351374391/100000000000000 : ℝ), (39639474982087/100000000000000 : ℝ), (28477086817949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(394261359/5000000000 : ℝ)|^4123 ≤ (3406351374391/100000000000000 : ℝ)^3099
        have hw : |(394261359/5000000000 : ℝ)|=(394261359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4988132629/10000000000 : ℝ)|^4123 ≤ (39639474982087/100000000000000 : ℝ)^3099
        have hw : |(-4988132629/10000000000 : ℝ)|=(4988132629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6550039561/10000000000 : ℝ)|^4123 ≤ (28477086817949/50000000000000 : ℝ)^3099
        have hw : |(6550039561/10000000000 : ℝ)|=(6550039561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_10 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1232301/15625000 : ℝ)*x 0 + (1310085231/2000000000 : ℝ)*x 1 + (-4987628109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232301/15625000 : ℝ)^4123 ≤ (3407213054369/100000000000000 : ℝ)^3099 := by
    have hnat : (1232301 : ℕ)^4123*100000000000000^3099 ≤ 3407213054369^3099*15625000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232301 15625000 3407213054369 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310085231/2000000000 : ℝ)^4123 ≤ (28479322977251/50000000000000 : ℝ)^3099 := by
    have hnat : (1310085231 : ℕ)^4123*50000000000000^3099 ≤ 28479322977251^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310085231 2000000000 28479322977251 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4987628109/10000000000 : ℝ)^4123 ≤ (9908535246203/25000000000000 : ℝ)^3099 := by
    have hnat : (4987628109 : ℕ)^4123*25000000000000^3099 ≤ 9908535246203^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987628109 10000000000 9908535246203 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1232301/15625000 : ℝ), (1310085231/2000000000 : ℝ), (-4987628109/10000000000 : ℝ)] ![(3407213054369/100000000000000 : ℝ), (28479322977251/50000000000000 : ℝ), (9908535246203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1232301/15625000 : ℝ)|^4123 ≤ (3407213054369/100000000000000 : ℝ)^3099
        have hw : |(1232301/15625000 : ℝ)|=(1232301/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310085231/2000000000 : ℝ)|^4123 ≤ (28479322977251/50000000000000 : ℝ)^3099
        have hw : |(1310085231/2000000000 : ℝ)|=(1310085231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4987628109/10000000000 : ℝ)|^4123 ≤ (9908535246203/25000000000000 : ℝ)^3099
        have hw : |(-4987628109/10000000000 : ℝ)|=(4987628109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s2_11 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80794029/500000000 : ℝ)*x 0 + (2768613609/5000000000 : ℝ)*x 1 + (5542357197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80794029/500000000 : ℝ)^4123 ≤ (1769597866227/20000000000000 : ℝ)^3099 := by
    have hnat : (80794029 : ℕ)^4123*20000000000000^3099 ≤ 1769597866227^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80794029 500000000 1769597866227 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768613609/5000000000 : ℝ)^4123 ≤ (45547930303149/100000000000000 : ℝ)^3099 := by
    have hnat : (2768613609 : ℕ)^4123*100000000000000^3099 ≤ 45547930303149^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768613609 5000000000 45547930303149 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5542357197/10000000000 : ℝ)^4123 ≤ (45604080347561/100000000000000 : ℝ)^3099 := by
    have hnat : (5542357197 : ℕ)^4123*100000000000000^3099 ≤ 45604080347561^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542357197 10000000000 45604080347561 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80794029/500000000 : ℝ), (2768613609/5000000000 : ℝ), (5542357197/10000000000 : ℝ)] ![(1769597866227/20000000000000 : ℝ), (45547930303149/100000000000000 : ℝ), (45604080347561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80794029/500000000 : ℝ)|^4123 ≤ (1769597866227/20000000000000 : ℝ)^3099
        have hw : |(80794029/500000000 : ℝ)|=(80794029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768613609/5000000000 : ℝ)|^4123 ≤ (45547930303149/100000000000000 : ℝ)^3099
        have hw : |(2768613609/5000000000 : ℝ)|=(2768613609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5542357197/10000000000 : ℝ)|^4123 ≤ (45604080347561/100000000000000 : ℝ)^3099
        have hw : |(5542357197/10000000000 : ℝ)|=(5542357197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (321/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1081/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1049/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (321/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (321/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (321/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (321/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (321/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (321/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (321/6250 : ℝ) ^ (8245/2048 : ℝ) ≤ (322182873218949/50000000000000000000 : ℝ) := by
    have hpowers : (321/6250 : ℝ)^8245 ≤ (322182873218949/50000000000000000000 : ℝ)^2048 := by
      have hnat : (321 : ℕ)^8245*50000000000000000000^2048 ≤ 322182873218949^2048*6250^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        321 6250 322182873218949 50000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (321/6250 : ℝ)) (X := (322182873218949/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20853/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (45393639900019383/25000000000000000000 : ℝ) := by
    have hpowers : (20853/100000 : ℝ)^8245 ≤ (45393639900019383/25000000000000000000 : ℝ)^2048 := by
      have hnat : (20853 : ℕ)^8245*25000000000000000000^2048 ≤ 45393639900019383^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20853 100000 45393639900019383 25000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20853/100000 : ℝ)) (X := (45393639900019383/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000322182873218949/25000000000000000000 : ℝ) ≤ (2000006402205737/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (25000322182873218949/25000000000000000000 : ℝ)^2048 ≤ (2000006402205737/2000000000000000 : ℝ)^8245 := by
      have hnat : (25000322182873218949 : ℕ)^2048*2000000000000000^8245 ≤ 2000006402205737^8245*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000322182873218949 25000000000000000000 2000006402205737 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006402205737/2000000000000000 : ℝ)) (X := (25000322182873218949/25000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10018221892534651543/10000000000000000000 : ℝ) ≤ (2000904618749679/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (10018221892534651543/10000000000000000000 : ℝ)^2048 ≤ (2000904618749679/2000000000000000 : ℝ)^8245 := by
      have hnat : (10018221892534651543 : ℕ)^2048*2000000000000000^8245 ≤ 2000904618749679^8245*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10018221892534651543 10000000000000000000 2000904618749679 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000904618749679/2000000000000000 : ℝ)) (X := (10018221892534651543/10000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12545393639900019383/12500000000000000000 : ℝ) ≤ (2001802835293621/2000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (12545393639900019383/12500000000000000000 : ℝ)^2048 ≤ (2001802835293621/2000000000000000 : ℝ)^8245 := by
      have hnat : (12545393639900019383 : ℕ)^2048*2000000000000000^8245 ≤ 2001802835293621^8245*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12545393639900019383 12500000000000000000 2001802835293621 2000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001802835293621/2000000000000000 : ℝ)) (X := (12545393639900019383/12500000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(322182873218949/50000000000000000000 : ℝ) ≤ ((2094991609541879747/2095600000000000000 : ℝ)+2*(449108271971/157170000000000 : ℝ)*(321/6250 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (2094991609541879747/2095600000000000000 : ℝ)+2*(449108271971/157170000000000 : ℝ)*(321/6250 : ℝ)=(2000006402205737/2000000000000000 : ℝ) by norm_num, show 1+2*(322182873218949/50000000000000000000 : ℝ)=(25000322182873218949/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45393639900019383/25000000000000000000 : ℝ)+(322182873218949/50000000000000000000 : ℝ) ≤ ((2094991609541879747/2095600000000000000 : ℝ)+(449108271971/157170000000000 : ℝ)*((20853/100000 : ℝ)+(321/6250 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (2094991609541879747/2095600000000000000 : ℝ)+(449108271971/157170000000000 : ℝ)*((20853/100000 : ℝ)+(321/6250 : ℝ))=(2000904618749679/2000000000000000 : ℝ) by norm_num, show 1+(45393639900019383/25000000000000000000 : ℝ)+(322182873218949/50000000000000000000 : ℝ)=(10018221892534651543/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45393639900019383/25000000000000000000 : ℝ) ≤ ((2094991609541879747/2095600000000000000 : ℝ)+2*(449108271971/157170000000000 : ℝ)*(20853/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (2094991609541879747/2095600000000000000 : ℝ)+2*(449108271971/157170000000000 : ℝ)*(20853/100000 : ℝ)=(2001802835293621/2000000000000000 : ℝ) by norm_num, show 1+2*(45393639900019383/25000000000000000000 : ℝ)=(12545393639900019383/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2094991609541879747/2095600000000000000 : ℝ)*(X 1 0+X 2 0)+(449108271971/157170000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (321/6250 : ℝ)) (hi := (20853/100000 : ℝ)) (c := (2094991609541879747/2095600000000000000 : ℝ)) (alpha := (449108271971/157170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2094991609541879747/2095600000000000000 : ℝ)*(X 0 1+X 2 1)+(449108271971/157170000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (321/6250 : ℝ)) (hi := (20853/100000 : ℝ)) (c := (2094991609541879747/2095600000000000000 : ℝ)) (alpha := (449108271971/157170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2094991609541879747/2095600000000000000 : ℝ)*(X 0 2+X 1 2)+(449108271971/157170000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (321/6250 : ℝ)) (hi := (20853/100000 : ℝ)) (c := (2094991609541879747/2095600000000000000 : ℝ)) (alpha := (449108271971/157170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136845243/625000000 : ℝ)*X 0 0+(5528613971/10000000000 : ℝ)*X 0 1+(5143568527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377786813/10000000000 : ℝ)*X 1 0+(-597610081/2500000000 : ℝ)*X 1 1+(5143569931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688893561/5000000000 : ℝ)*X 2 0+(2571784677/5000000000 : ℝ)*X 2 1+(-1195220331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182261417/5000000000 : ℝ)*X 0 0+(400459219/1000000000 : ℝ)*X 0 1+(4757275749/10000000000 : ℝ)*X 0 2+(2182261417/5000000000 : ℝ)*X 1 0+(400459219/1000000000 : ℝ)*X 1 1+(4757275749/10000000000 : ℝ)*X 1 2+(2182261417/5000000000 : ℝ)*X 2 0+(400459219/1000000000 : ℝ)*X 2 1+(4757275749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094827053/5000000000 : ℝ)*X 0 0+(514639619/1000000000 : ℝ)*X 0 1+(5525756579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280687279/10000000000 : ℝ)*X 1 0+(-2008254167/10000000000 : ℝ)*X 1 1+(5525756651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640343757/5000000000 : ℝ)*X 2 0+(690719561/1250000000 : ℝ)*X 2 1+(-2008254071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182388729/5000000000 : ℝ)*X 0 0+(4751751279/10000000000 : ℝ)*X 0 1+(4010175801/10000000000 : ℝ)*X 0 2+(2182388729/5000000000 : ℝ)*X 1 0+(4751751279/10000000000 : ℝ)*X 1 1+(4010175801/10000000000 : ℝ)*X 1 2+(2182388729/5000000000 : ℝ)*X 2 0+(4751751279/10000000000 : ℝ)*X 2 1+(4010175801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((73/1000000000 : ℝ)*X 0 0+(742322109/1250000000 : ℝ)*X 0 1+(1485001721/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((394261359/5000000000 : ℝ)*X 1 0+(-4988132629/10000000000 : ℝ)*X 1 1+(6550039561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1232301/15625000 : ℝ)*X 2 0+(1310085231/2000000000 : ℝ)*X 2 1+(-4987628109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((80794029/500000000 : ℝ)*X 0 0+(2768613609/5000000000 : ℝ)*X 0 1+(5542357197/10000000000 : ℝ)*X 0 2+(80794029/500000000 : ℝ)*X 1 0+(2768613609/5000000000 : ℝ)*X 1 1+(5542357197/10000000000 : ℝ)*X 1 2+(80794029/500000000 : ℝ)*X 2 0+(2768613609/5000000000 : ℝ)*X 2 1+(5542357197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1920644343640158175333269/845000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (490711997484793/25000000000000 : ℝ)*(major0) + (490711997484793/25000000000000 : ℝ)*(major1) + (490711997484793/25000000000000 : ℝ)*(major2) + (51942099983829/2000000000000 : ℝ)*(sp0) + (324639343115537/12500000000000 : ℝ)*(sp1) + (129855568317907/5000000000000 : ℝ)*(sp2) + (1328579794877173/100000000000000 : ℝ)*(sp3) + (9345411809/100000000000000 : ℝ)*(sp4) + (3272931817/100000000000000 : ℝ)*(sp6) + (364621311/100000000000000 : ℝ)*(sp7) + (400302797/50000000000000 : ℝ)*(sp8) + (400284557/100000000000000 : ℝ)*(sp9) + (31619931/6250000000000 : ℝ)*(sp10) + (299702967/50000000000000 : ℝ)*(sp11) + (1328580758904417/100000000000000 : ℝ)*(f.failure) + (1298557572604427/50000000000000 : ℝ)*(f.sum) + (320867802019/253500000000000000000000000 : ℝ)*base66 + (37281234175830577/5070000000000000000000000000000 : ℝ)*base68 + (40979542958310577/5070000000000000000000000000000 : ℝ)*base70 + (43423727450280577/5070000000000000000000000000000 : ℝ)*base72 + (817436096527/253500000000000000000000000 : ℝ)*base74 + (32572765026030577/5070000000000000000000000000000 : ℝ)*base76 + (24665421452160577/5070000000000000000000000000000 : ℝ)*base78 + (40396077441390577/5070000000000000000000000000000 : ℝ)*base80 + (1469383002941/507000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21396847/10000000000000000000000 : ℝ)*base90 + (21396847/10000000000000000000000 : ℝ)*base92 + (21396847/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251846518723057939195406259/26195000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498062378548167/25000000000000 : ℝ)*(major0) + (498062378548167/25000000000000 : ℝ)*(major1) + (498062378548167/25000000000000 : ℝ)*(major2) + (690376763/100000000000000 : ℝ)*(sp1) + (137743969/100000000000000 : ℝ)*(sp2) + (1208467/6250000000000 : ℝ)*(sp3) + (2636016085773307/100000000000000 : ℝ)*(sp4) + (13180079699491/500000000000 : ℝ)*(sp5) + (164751022909811/6250000000000 : ℝ)*(sp6) + (269696110139731/20000000000000 : ℝ)*(sp7) + (517827517/50000000000000 : ℝ)*(sp8) + (245576689/50000000000000 : ℝ)*(sp9) + (154281849/25000000000000 : ℝ)*(sp10) + (1016446279/100000000000000 : ℝ)*(sp11) + (674240793240203/50000000000000 : ℝ)*(f.failure) + (1318008560714171/50000000000000 : ℝ)*(f.sum) + (436244167019/654875000000000000000000000 : ℝ)*base66 + (336333592492283749/52390000000000000000000000000000 : ℝ)*base67 + (343351875817583749/52390000000000000000000000000000 : ℝ)*base69 + (515401315525443749/52390000000000000000000000000000 : ℝ)*base71 + (1924733046979/1047800000000000000000000000 : ℝ)*base74 + (359459820370803749/52390000000000000000000000000000 : ℝ)*base75 + (324683651505833749/52390000000000000000000000000000 : ℝ)*base77 + (488549870921043749/52390000000000000000000000000000 : ℝ)*base79 + (129286681737/65487500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21577573/5000000000000000000000 : ℝ)*base90 + (21577573/5000000000000000000000 : ℝ)*base92 + (21577573/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1053_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (321/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1053_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1053_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1053_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1053_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1049/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
