-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:35.288622+00:00
-- url     : https://prove2.me/submissions/d2a0d304-8886-47b1-bf6e-87658ed68b33

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
theorem support_rectangle_w1415_s6_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982544821/10000000000 : ℝ)*x 0 + (2704472513/5000000000 : ℝ)*x 1 + (5246581841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982544821/10000000000 : ℝ)^4375 ≤ (3022791095453/25000000000000 : ℝ)^3351 := by
    have hnat : (1982544821 : ℕ)^4375*25000000000000^3351 ≤ 3022791095453^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982544821 10000000000 3022791095453 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704472513/5000000000 : ℝ)^4375 ≤ (2801799220491/6250000000000 : ℝ)^3351 := by
    have hnat : (2704472513 : ℕ)^4375*6250000000000^3351 ≤ 2801799220491^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704472513 5000000000 2801799220491 6250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246581841/10000000000 : ℝ)^4375 ≤ (10770012017017/25000000000000 : ℝ)^3351 := by
    have hnat : (5246581841 : ℕ)^4375*25000000000000^3351 ≤ 10770012017017^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246581841 10000000000 10770012017017 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982544821/10000000000 : ℝ), (2704472513/5000000000 : ℝ), (5246581841/10000000000 : ℝ)] ![(3022791095453/25000000000000 : ℝ), (2801799220491/6250000000000 : ℝ), (10770012017017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982544821/10000000000 : ℝ)|^4375 ≤ (3022791095453/25000000000000 : ℝ)^3351
        have hw : |(-1982544821/10000000000 : ℝ)|=(1982544821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704472513/5000000000 : ℝ)|^4375 ≤ (2801799220491/6250000000000 : ℝ)^3351
        have hw : |(2704472513/5000000000 : ℝ)|=(2704472513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246581841/10000000000 : ℝ)|^4375 ≤ (10770012017017/25000000000000 : ℝ)^3351
        have hw : |(5246581841/10000000000 : ℝ)|=(5246581841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347619191/10000000000 : ℝ)*x 0 + (-2065216267/10000000000 : ℝ)*x 1 + (2623290929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347619191/10000000000 : ℝ)^4375 ≤ (11041590694249/25000000000000 : ℝ)^3351 := by
    have hnat : (5347619191 : ℕ)^4375*25000000000000^3351 ≤ 11041590694249^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347619191 10000000000 11041590694249 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065216267/10000000000 : ℝ)^4375 ≤ (12753588957001/100000000000000 : ℝ)^3351 := by
    have hnat : (2065216267 : ℕ)^4375*100000000000000^3351 ≤ 12753588957001^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065216267 10000000000 12753588957001 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623290929/5000000000 : ℝ)^4375 ≤ (43080048250311/100000000000000 : ℝ)^3351 := by
    have hnat : (2623290929 : ℕ)^4375*100000000000000^3351 ≤ 43080048250311^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623290929 5000000000 43080048250311 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347619191/10000000000 : ℝ), (-2065216267/10000000000 : ℝ), (2623290929/5000000000 : ℝ)] ![(11041590694249/25000000000000 : ℝ), (12753588957001/100000000000000 : ℝ), (43080048250311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347619191/10000000000 : ℝ)|^4375 ≤ (11041590694249/25000000000000 : ℝ)^3351
        have hw : |(5347619191/10000000000 : ℝ)|=(5347619191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065216267/10000000000 : ℝ)|^4375 ≤ (12753588957001/100000000000000 : ℝ)^3351
        have hw : |(-2065216267/10000000000 : ℝ)|=(2065216267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623290929/5000000000 : ℝ)|^4375 ≤ (43080048250311/100000000000000 : ℝ)^3351
        have hw : |(2623290929/5000000000 : ℝ)|=(2623290929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673809593/5000000000 : ℝ)*x 0 + (655822729/1250000000 : ℝ)*x 1 + (-2065216309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673809593/5000000000 : ℝ)^4375 ≤ (44166362723081/100000000000000 : ℝ)^3351 := by
    have hnat : (2673809593 : ℕ)^4375*100000000000000^3351 ≤ 44166362723081^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673809593 5000000000 44166362723081 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655822729/1250000000 : ℝ)^4375 ≤ (21540023985793/50000000000000 : ℝ)^3351 := by
    have hnat : (655822729 : ℕ)^4375*50000000000000^3351 ≤ 21540023985793^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655822729 1250000000 21540023985793 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065216309/10000000000 : ℝ)^4375 ≤ (6376794647813/50000000000000 : ℝ)^3351 := by
    have hnat : (2065216309 : ℕ)^4375*50000000000000^3351 ≤ 6376794647813^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065216309 10000000000 6376794647813 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673809593/5000000000 : ℝ), (655822729/1250000000 : ℝ), (-2065216309/10000000000 : ℝ)] ![(44166362723081/100000000000000 : ℝ), (21540023985793/50000000000000 : ℝ), (6376794647813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673809593/5000000000 : ℝ)|^4375 ≤ (44166362723081/100000000000000 : ℝ)^3351
        have hw : |(2673809593/5000000000 : ℝ)|=(2673809593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655822729/1250000000 : ℝ)|^4375 ≤ (21540023985793/50000000000000 : ℝ)^3351
        have hw : |(655822729/1250000000 : ℝ)|=(655822729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065216309/10000000000 : ℝ)|^4375 ≤ (6376794647813/50000000000000 : ℝ)^3351
        have hw : |(-2065216309/10000000000 : ℝ)|=(2065216309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307886251/10000000000 : ℝ)*x 0 + (4136370307/10000000000 : ℝ)*x 1 + (448581533/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307886251/10000000000 : ℝ)^4375 ≤ (16652235311451/50000000000000 : ℝ)^3351 := by
    have hnat : (4307886251 : ℕ)^4375*50000000000000^3351 ≤ 16652235311451^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307886251 10000000000 16652235311451 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136370307/10000000000 : ℝ)^4375 ≤ (986996996263/3125000000000 : ℝ)^3351 := by
    have hnat : (4136370307 : ℕ)^4375*3125000000000^3351 ≤ 986996996263^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136370307 10000000000 986996996263 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448581533/1000000000 : ℝ)^4375 ≤ (7022325096021/20000000000000 : ℝ)^3351 := by
    have hnat : (448581533 : ℕ)^4375*20000000000000^3351 ≤ 7022325096021^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448581533 1000000000 7022325096021 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307886251/10000000000 : ℝ), (4136370307/10000000000 : ℝ), (448581533/1000000000 : ℝ)] ![(16652235311451/50000000000000 : ℝ), (986996996263/3125000000000 : ℝ), (7022325096021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307886251/10000000000 : ℝ)|^4375 ≤ (16652235311451/50000000000000 : ℝ)^3351
        have hw : |(4307886251/10000000000 : ℝ)|=(4307886251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136370307/10000000000 : ℝ)|^4375 ≤ (986996996263/3125000000000 : ℝ)^3351
        have hw : |(4136370307/10000000000 : ℝ)|=(4136370307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448581533/1000000000 : ℝ)|^4375 ≤ (7022325096021/20000000000000 : ℝ)^3351
        have hw : |(448581533/1000000000 : ℝ)|=(448581533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982556291/10000000000 : ℝ)*x 0 + (5247166709/10000000000 : ℝ)*x 1 + (5408357121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982556291/10000000000 : ℝ)^4375 ≤ (604562785581/5000000000000 : ℝ)^3351 := by
    have hnat : (1982556291 : ℕ)^4375*5000000000000^3351 ≤ 604562785581^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982556291 10000000000 604562785581 5000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247166709/10000000000 : ℝ)^4375 ≤ (10771579520891/25000000000000 : ℝ)^3351 := by
    have hnat : (5247166709 : ℕ)^4375*25000000000000^3351 ≤ 10771579520891^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247166709 10000000000 10771579520891 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408357121/10000000000 : ℝ)^4375 ≤ (5602803274603/12500000000000 : ℝ)^3351 := by
    have hnat : (5408357121 : ℕ)^4375*12500000000000^3351 ≤ 5602803274603^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408357121 10000000000 5602803274603 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982556291/10000000000 : ℝ), (5247166709/10000000000 : ℝ), (5408357121/10000000000 : ℝ)] ![(604562785581/5000000000000 : ℝ), (10771579520891/25000000000000 : ℝ), (5602803274603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982556291/10000000000 : ℝ)|^4375 ≤ (604562785581/5000000000000 : ℝ)^3351
        have hw : |(-1982556291/10000000000 : ℝ)|=(1982556291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247166709/10000000000 : ℝ)|^4375 ≤ (10771579520891/25000000000000 : ℝ)^3351
        have hw : |(5247166709/10000000000 : ℝ)|=(5247166709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408357121/10000000000 : ℝ)|^4375 ≤ (5602803274603/12500000000000 : ℝ)^3351
        have hw : |(5408357121/10000000000 : ℝ)|=(5408357121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305467707/10000000000 : ℝ)*x 0 + (-1903441003/10000000000 : ℝ)*x 1 + (2704178553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305467707/10000000000 : ℝ)^4375 ≤ (43712396753127/100000000000000 : ℝ)^3351 := by
    have hnat : (5305467707 : ℕ)^4375*100000000000000^3351 ≤ 43712396753127^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305467707 10000000000 43712396753127 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903441003/10000000000 : ℝ)^4375 ≤ (11465177196861/100000000000000 : ℝ)^3351 := by
    have hnat : (1903441003 : ℕ)^4375*100000000000000^3351 ≤ 11465177196861^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903441003 10000000000 11465177196861 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704178553/5000000000 : ℝ)^4375 ≤ (22411213017261/50000000000000 : ℝ)^3351 := by
    have hnat : (2704178553 : ℕ)^4375*50000000000000^3351 ≤ 22411213017261^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704178553 5000000000 22411213017261 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305467707/10000000000 : ℝ), (-1903441003/10000000000 : ℝ), (2704178553/5000000000 : ℝ)] ![(43712396753127/100000000000000 : ℝ), (11465177196861/100000000000000 : ℝ), (22411213017261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305467707/10000000000 : ℝ)|^4375 ≤ (43712396753127/100000000000000 : ℝ)^3351
        have hw : |(5305467707/10000000000 : ℝ)|=(5305467707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903441003/10000000000 : ℝ)|^4375 ≤ (11465177196861/100000000000000 : ℝ)^3351
        have hw : |(-1903441003/10000000000 : ℝ)|=(1903441003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704178553/5000000000 : ℝ)|^4375 ≤ (22411213017261/50000000000000 : ℝ)^3351
        have hw : |(2704178553/5000000000 : ℝ)|=(2704178553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061093541/2000000000 : ℝ)*x 0 + (1081671421/2000000000 : ℝ)*x 1 + (-1903441007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061093541/2000000000 : ℝ)^4375 ≤ (43712396731613/100000000000000 : ℝ)^3351 := by
    have hnat : (1061093541 : ℕ)^4375*100000000000000^3351 ≤ 43712396731613^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061093541 2000000000 43712396731613 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081671421/2000000000 : ℝ)^4375 ≤ (22411213011851/50000000000000 : ℝ)^3351 := by
    have hnat : (1081671421 : ℕ)^4375*50000000000000^3351 ≤ 22411213011851^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081671421 2000000000 22411213011851 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903441007/10000000000 : ℝ)^4375 ≤ (5732588614159/50000000000000 : ℝ)^3351 := by
    have hnat : (1903441007 : ℕ)^4375*50000000000000^3351 ≤ 5732588614159^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903441007 10000000000 5732588614159 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061093541/2000000000 : ℝ), (1081671421/2000000000 : ℝ), (-1903441007/10000000000 : ℝ)] ![(43712396731613/100000000000000 : ℝ), (22411213011851/50000000000000 : ℝ), (5732588614159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061093541/2000000000 : ℝ)|^4375 ≤ (43712396731613/100000000000000 : ℝ)^3351
        have hw : |(1061093541/2000000000 : ℝ)|=(1061093541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081671421/2000000000 : ℝ)|^4375 ≤ (22411213011851/50000000000000 : ℝ)^3351
        have hw : |(1081671421/2000000000 : ℝ)|=(1081671421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903441007/10000000000 : ℝ)|^4375 ≤ (5732588614159/50000000000000 : ℝ)^3351
        have hw : |(-1903441007/10000000000 : ℝ)|=(1903441007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s6_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076977727/2500000000 : ℝ)*x 0 + (560569563/1250000000 : ℝ)*x 1 + (4137635641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076977727/2500000000 : ℝ)^4375 ≤ (6660943899727/20000000000000 : ℝ)^3351 := by
    have hnat : (1076977727 : ℕ)^4375*20000000000000^3351 ≤ 6660943899727^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076977727 2500000000 6660943899727 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560569563/1250000000 : ℝ)^4375 ≤ (2193672621711/6250000000000 : ℝ)^3351 := by
    have hnat : (560569563 : ℕ)^4375*6250000000000^3351 ≤ 2193672621711^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560569563 1250000000 2193672621711 6250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137635641/10000000000 : ℝ)^4375 ≤ (31596518539019/100000000000000 : ℝ)^3351 := by
    have hnat : (4137635641 : ℕ)^4375*100000000000000^3351 ≤ 31596518539019^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137635641 10000000000 31596518539019 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076977727/2500000000 : ℝ), (560569563/1250000000 : ℝ), (4137635641/10000000000 : ℝ)] ![(6660943899727/20000000000000 : ℝ), (2193672621711/6250000000000 : ℝ), (31596518539019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076977727/2500000000 : ℝ)|^4375 ≤ (6660943899727/20000000000000 : ℝ)^3351
        have hw : |(1076977727/2500000000 : ℝ)|=(1076977727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560569563/1250000000 : ℝ)|^4375 ≤ (2193672621711/6250000000000 : ℝ)^3351
        have hw : |(560569563/1250000000 : ℝ)|=(560569563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137635641/10000000000 : ℝ)|^4375 ≤ (31596518539019/100000000000000 : ℝ)^3351
        have hw : |(4137635641/10000000000 : ℝ)|=(4137635641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (9044575264500723/100000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^2187 ≤ (9044575264500723/100000000000000000000 : ℝ)^512 := by
      have hnat : (11307 : ℕ)^2187*100000000000000000000^512 ≤ 9044575264500723^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 9044575264500723 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (9044575264500723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (2187/512 : ℝ) ≤ (28184550137865379/100000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^2187 ≤ (28184550137865379/100000000000000000000 : ℝ)^512 := by
      have hnat : (7377 : ℕ)^2187*100000000000000000000^512 ≤ 28184550137865379^512*50000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 28184550137865379 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (28184550137865379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009044575264500723/50000000000000000000 : ℝ) ≤ (5000211728476719/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50009044575264500723/50000000000000000000 : ℝ)^512 ≤ (5000211728476719/5000000000000000 : ℝ)^2187 := by
      have hnat : (50009044575264500723 : ℕ)^512*5000000000000000^2187 ≤ 5000211728476719^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009044575264500723 50000000000000000000 5000211728476719 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211728476719/5000000000000000 : ℝ)) (X := (50009044575264500723/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018614562701183051/50000000000000000000 : ℝ) ≤ (62505446557867/62500000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50018614562701183051/50000000000000000000 : ℝ)^512 ≤ (62505446557867/62500000000000 : ℝ)^2187 := by
      have hnat : (50018614562701183051 : ℕ)^512*62500000000000^2187 ≤ 62505446557867^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018614562701183051 50000000000000000000 62505446557867 62500000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62505446557867/62500000000000 : ℝ)) (X := (50018614562701183051/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028184550137865379/50000000000000000000 : ℝ) ≤ (5000659720782001/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50028184550137865379/50000000000000000000 : ℝ)^512 ≤ (5000659720782001/5000000000000000 : ℝ)^2187 := by
      have hnat : (50028184550137865379 : ℕ)^512*5000000000000000^2187 ≤ 5000659720782001^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028184550137865379 50000000000000000000 5000659720782001 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000659720782001/5000000000000000 : ℝ)) (X := (50028184550137865379/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9044575264500723/100000000000000000000 : ℝ) ≤ ((5743554793021142273/5745000000000000000 : ℝ)+2*(223996152641/172350000000000 : ℝ)*(11307/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (5743554793021142273/5745000000000000000 : ℝ)+2*(223996152641/172350000000000 : ℝ)*(11307/100000 : ℝ)=(5000211728476719/5000000000000000 : ℝ) by norm_num, show 1+2*(9044575264500723/100000000000000000000 : ℝ)=(50009044575264500723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28184550137865379/100000000000000000000 : ℝ)+(9044575264500723/100000000000000000000 : ℝ) ≤ ((5743554793021142273/5745000000000000000 : ℝ)+(223996152641/172350000000000 : ℝ)*((7377/50000 : ℝ)+(11307/100000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (5743554793021142273/5745000000000000000 : ℝ)+(223996152641/172350000000000 : ℝ)*((7377/50000 : ℝ)+(11307/100000 : ℝ))=(62505446557867/62500000000000 : ℝ) by norm_num, show 1+(28184550137865379/100000000000000000000 : ℝ)+(9044575264500723/100000000000000000000 : ℝ)=(50018614562701183051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28184550137865379/100000000000000000000 : ℝ) ≤ ((5743554793021142273/5745000000000000000 : ℝ)+2*(223996152641/172350000000000 : ℝ)*(7377/50000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (5743554793021142273/5745000000000000000 : ℝ)+2*(223996152641/172350000000000 : ℝ)*(7377/50000 : ℝ)=(5000659720782001/5000000000000000 : ℝ) by norm_num, show 1+2*(28184550137865379/100000000000000000000 : ℝ)=(50028184550137865379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5743554793021142273/5745000000000000000 : ℝ)*(X 1 0+X 2 0)+(223996152641/172350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (5743554793021142273/5745000000000000000 : ℝ)) (alpha := (223996152641/172350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5743554793021142273/5745000000000000000 : ℝ)*(X 0 1+X 2 1)+(223996152641/172350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (5743554793021142273/5745000000000000000 : ℝ)) (alpha := (223996152641/172350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5743554793021142273/5745000000000000000 : ℝ)*(X 0 2+X 1 2)+(223996152641/172350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (5743554793021142273/5745000000000000000 : ℝ)) (alpha := (223996152641/172350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1982544821/10000000000 : ℝ)*X 0 0+(2704472513/5000000000 : ℝ)*X 0 1+(5246581841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347619191/10000000000 : ℝ)*X 1 0+(-2065216267/10000000000 : ℝ)*X 1 1+(2623290929/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673809593/5000000000 : ℝ)*X 2 0+(655822729/1250000000 : ℝ)*X 2 1+(-2065216309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307886251/10000000000 : ℝ)*X 0 0+(4136370307/10000000000 : ℝ)*X 0 1+(448581533/1000000000 : ℝ)*X 0 2+(4307886251/10000000000 : ℝ)*X 1 0+(4136370307/10000000000 : ℝ)*X 1 1+(448581533/1000000000 : ℝ)*X 1 2+(4307886251/10000000000 : ℝ)*X 2 0+(4136370307/10000000000 : ℝ)*X 2 1+(448581533/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1982556291/10000000000 : ℝ)*X 0 0+(5247166709/10000000000 : ℝ)*X 0 1+(5408357121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305467707/10000000000 : ℝ)*X 1 0+(-1903441003/10000000000 : ℝ)*X 1 1+(2704178553/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061093541/2000000000 : ℝ)*X 2 0+(1081671421/2000000000 : ℝ)*X 2 1+(-1903441007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076977727/2500000000 : ℝ)*X 0 0+(560569563/1250000000 : ℝ)*X 0 1+(4137635641/10000000000 : ℝ)*X 0 2+(1076977727/2500000000 : ℝ)*X 1 0+(560569563/1250000000 : ℝ)*X 1 1+(4137635641/10000000000 : ℝ)*X 1 2+(1076977727/2500000000 : ℝ)*X 2 0+(560569563/1250000000 : ℝ)*X 2 1+(4137635641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42908971707724784371045339/7181250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094058189/100000000000000 : ℝ)*(base19) + (40555269/4000000000000 : ℝ)*(base23) + (1989789/5000000000000 : ℝ)*(lower2) + (177577193/100000000000000 : ℝ)*(upper3) + (34796963/50000000000000 : ℝ)*(upper5) + (112759764731669/2500000000000 : ℝ)*(major0) + (112759764731669/2500000000000 : ℝ)*(major1) + (4510390589266761/100000000000000 : ℝ)*(major2) + (6159056656056487/100000000000000 : ℝ)*(sp0) + (1231815475796147/20000000000000 : ℝ)*(sp1) + (6159077459157199/100000000000000 : ℝ)*(sp2) + (1430845255085667/50000000000000 : ℝ)*(sp3) + (5454245609/25000000000000 : ℝ)*(sp4) + (2999037983/25000000000000 : ℝ)*(sp7) + (1430851253161633/50000000000000 : ℝ)*(f.failure) + (1539769618259731/25000000000000 : ℝ)*(f.sum) + (7328551114877/2154375000000000000000000000 : ℝ)*base65 + (257454732259061137/14362500000000000000000000000000 : ℝ)*base67 + (8484417731066163259/1723500000000000000000000000000000 : ℝ)*base69 + (60991007883723637/14362500000000000000000000000000 : ℝ)*base71 + (49186722751013/8617500000000000000000000000 : ℝ)*base73 + (10380196859048336741/1723500000000000000000000000000000 : ℝ)*base76 + (259541255057469089/43087500000000000000000000000000 : ℝ)*base78 + (118821684613655911/43087500000000000000000000000000 : ℝ)*base79 + (13952435719237/3447000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3813747/5000000000000000000000 : ℝ)*base90 + (3813747/5000000000000000000000 : ℝ)*base92 + (53813747/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1303972833112997834250177/149609375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1562466051/100000000000000 : ℝ)*(base19) + (208145337/12500000000000 : ℝ)*(base23) + (33073923/6250000000000 : ℝ)*(lower1) + (178940149/100000000000000 : ℝ)*(upper3) + (9896321/20000000000000 : ℝ)*(lower4) + (95378431/50000000000000 : ℝ)*(upper5) + (56789348181971/1250000000000 : ℝ)*(major0) + (56789348181971/1250000000000 : ℝ)*(major1) + (56789348181971/1250000000000 : ℝ)*(major2) + (1481445429/100000000000000 : ℝ)*(sp2) + (3101904723273251/50000000000000 : ℝ)*(sp4) + (124076157681609/2000000000000 : ℝ)*(sp5) + (6203806299938377/100000000000000 : ℝ)*(sp6) + (720621493010123/25000000000000 : ℝ)*(sp7) + (720621493010123/25000000000000 : ℝ)*(f.failure) + (3101904723273251/50000000000000 : ℝ)*(f.sum) + (3966616797593/1723500000000000000000000000 : ℝ)*base66 + (542065751736732251/21543750000000000000000000000000 : ℝ)*base68 + (190735753761207251/21543750000000000000000000000000 : ℝ)*base70 + (3905410357930482251/21543750000000000000000000000000 : ℝ)*base72 + (1086520696547/1723500000000000000000000000 : ℝ)*base74 + (3620701833774880249/21543750000000000000000000000000 : ℝ)*base75 + (133767318354001001/21543750000000000000000000000000 : ℝ)*base78 + (1019517142763501/21543750000000000000000000000000 : ℝ)*base80 + (399511771067/861750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (20703343/2500000000000000000000 : ℝ)*base89 + (20703343/2500000000000000000000 : ℝ)*base91 + (20703343/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1415_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s7_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347611793/10000000000 : ℝ)*x 0 + (5246609401/10000000000 : ℝ)*x 1 + (-2065189539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347611793/10000000000 : ℝ)^4375 ≤ (44166283005263/100000000000000 : ℝ)^3351 := by
    have hnat : (5347611793 : ℕ)^4375*100000000000000^3351 ≤ 44166283005263^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347611793 10000000000 44166283005263 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246609401/10000000000 : ℝ)^4375 ≤ (5385042939667/12500000000000 : ℝ)^3351 := by
    have hnat : (5246609401 : ℕ)^4375*12500000000000^3351 ≤ 5385042939667^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246609401 10000000000 5385042939667 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065189539/10000000000 : ℝ)^4375 ≤ (12753373462539/100000000000000 : ℝ)^3351 := by
    have hnat : (2065189539 : ℕ)^4375*100000000000000^3351 ≤ 12753373462539^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065189539 10000000000 12753373462539 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347611793/10000000000 : ℝ), (5246609401/10000000000 : ℝ), (-2065189539/10000000000 : ℝ)] ![(44166283005263/100000000000000 : ℝ), (5385042939667/12500000000000 : ℝ), (12753373462539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347611793/10000000000 : ℝ)|^4375 ≤ (44166283005263/100000000000000 : ℝ)^3351
        have hw : |(5347611793/10000000000 : ℝ)|=(5347611793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246609401/10000000000 : ℝ)|^4375 ≤ (5385042939667/12500000000000 : ℝ)^3351
        have hw : |(5246609401/10000000000 : ℝ)|=(5246609401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065189539/10000000000 : ℝ)|^4375 ≤ (12753373462539/100000000000000 : ℝ)^3351
        have hw : |(-2065189539/10000000000 : ℝ)|=(2065189539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s7_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-991279531/5000000000 : ℝ)*x 0 + (655899241/1250000000 : ℝ)*x 1 + (338020507/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991279531/5000000000 : ℝ)^4375 ≤ (2418255555143/20000000000000 : ℝ)^3351 := by
    have hnat : (991279531 : ℕ)^4375*20000000000000^3351 ≤ 2418255555143^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991279531 5000000000 2418255555143 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655899241/1250000000 : ℝ)^4375 ≤ (43086609887173/100000000000000 : ℝ)^3351 := by
    have hnat : (655899241 : ℕ)^4375*100000000000000^3351 ≤ 43086609887173^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655899241 1250000000 43086609887173 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338020507/625000000 : ℝ)^4375 ≤ (44822112315099/100000000000000 : ℝ)^3351 := by
    have hnat : (338020507 : ℕ)^4375*100000000000000^3351 ≤ 44822112315099^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338020507 625000000 44822112315099 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-991279531/5000000000 : ℝ), (655899241/1250000000 : ℝ), (338020507/625000000 : ℝ)] ![(2418255555143/20000000000000 : ℝ), (43086609887173/100000000000000 : ℝ), (44822112315099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-991279531/5000000000 : ℝ)|^4375 ≤ (2418255555143/20000000000000 : ℝ)^3351
        have hw : |(-991279531/5000000000 : ℝ)|=(991279531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655899241/1250000000 : ℝ)|^4375 ≤ (43086609887173/100000000000000 : ℝ)^3351
        have hw : |(655899241/1250000000 : ℝ)|=(655899241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338020507/625000000 : ℝ)|^4375 ≤ (44822112315099/100000000000000 : ℝ)^3351
        have hw : |(338020507/625000000 : ℝ)|=(338020507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s7_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061095007/2000000000 : ℝ)*x 0 + (-1903470889/10000000000 : ℝ)*x 1 + (54083281/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061095007/2000000000 : ℝ)^4375 ≤ (21856237789621/50000000000000 : ℝ)^3351 := by
    have hnat : (1061095007 : ℕ)^4375*50000000000000^3351 ≤ 21856237789621^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061095007 2000000000 21856237789621 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903470889/10000000000 : ℝ)^4375 ≤ (358294131929/3125000000000 : ℝ)^3351 := by
    have hnat : (1903470889 : ℕ)^4375*3125000000000^3351 ≤ 358294131929^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903470889 10000000000 358294131929 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54083281/100000000 : ℝ)^4375 ≤ (44822112185257/100000000000000 : ℝ)^3351 := by
    have hnat : (54083281 : ℕ)^4375*100000000000000^3351 ≤ 44822112185257^3351*100000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54083281 100000000 44822112185257 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061095007/2000000000 : ℝ), (-1903470889/10000000000 : ℝ), (54083281/100000000 : ℝ)] ![(21856237789621/50000000000000 : ℝ), (358294131929/3125000000000 : ℝ), (44822112185257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061095007/2000000000 : ℝ)|^4375 ≤ (21856237789621/50000000000000 : ℝ)^3351
        have hw : |(1061095007/2000000000 : ℝ)|=(1061095007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903470889/10000000000 : ℝ)|^4375 ≤ (358294131929/3125000000000 : ℝ)^3351
        have hw : |(-1903470889/10000000000 : ℝ)|=(1903470889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54083281/100000000 : ℝ)|^4375 ≤ (44822112185257/100000000000000 : ℝ)^3351
        have hw : |(54083281/100000000 : ℝ)|=(54083281/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s7_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652737537/5000000000 : ℝ)*x 0 + (676041009/1250000000 : ℝ)*x 1 + (-1903470873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652737537/5000000000 : ℝ)^4375 ≤ (43712475998759/100000000000000 : ℝ)^3351 := by
    have hnat : (2652737537 : ℕ)^4375*100000000000000^3351 ≤ 43712475998759^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652737537 5000000000 43712475998759 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676041009/1250000000 : ℝ)^4375 ≤ (44822111882293/100000000000000 : ℝ)^3351 := by
    have hnat : (676041009 : ℕ)^4375*100000000000000^3351 ≤ 44822111882293^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676041009 1250000000 44822111882293 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903470873/10000000000 : ℝ)^4375 ≤ (11465412095903/100000000000000 : ℝ)^3351 := by
    have hnat : (1903470873 : ℕ)^4375*100000000000000^3351 ≤ 11465412095903^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903470873 10000000000 11465412095903 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652737537/5000000000 : ℝ), (676041009/1250000000 : ℝ), (-1903470873/10000000000 : ℝ)] ![(43712475998759/100000000000000 : ℝ), (44822111882293/100000000000000 : ℝ), (11465412095903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652737537/5000000000 : ℝ)|^4375 ≤ (43712475998759/100000000000000 : ℝ)^3351
        have hw : |(2652737537/5000000000 : ℝ)|=(2652737537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676041009/1250000000 : ℝ)|^4375 ≤ (44822111882293/100000000000000 : ℝ)^3351
        have hw : |(676041009/1250000000 : ℝ)|=(676041009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903470873/10000000000 : ℝ)|^4375 ≤ (11465412095903/100000000000000 : ℝ)^3351
        have hw : |(-1903470873/10000000000 : ℝ)|=(1903470873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s7_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307912913/10000000000 : ℝ)*x 0 + (2242247881/5000000000 : ℝ)*x 1 + (2068847933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307912913/10000000000 : ℝ)^4375 ≤ (33304739736147/100000000000000 : ℝ)^3351 := by
    have hnat : (4307912913 : ℕ)^4375*100000000000000^3351 ≤ 33304739736147^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307912913 10000000000 33304739736147 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242247881/5000000000 : ℝ)^4375 ≤ (8774535318143/25000000000000 : ℝ)^3351 := by
    have hnat : (2242247881 : ℕ)^4375*25000000000000^3351 ≤ 8774535318143^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242247881 5000000000 8774535318143 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068847933/5000000000 : ℝ)^4375 ≤ (31597118977327/100000000000000 : ℝ)^3351 := by
    have hnat : (2068847933 : ℕ)^4375*100000000000000^3351 ≤ 31597118977327^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068847933 5000000000 31597118977327 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307912913/10000000000 : ℝ), (2242247881/5000000000 : ℝ), (2068847933/5000000000 : ℝ)] ![(33304739736147/100000000000000 : ℝ), (8774535318143/25000000000000 : ℝ), (31597118977327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307912913/10000000000 : ℝ)|^4375 ≤ (33304739736147/100000000000000 : ℝ)^3351
        have hw : |(4307912913/10000000000 : ℝ)|=(4307912913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242247881/5000000000 : ℝ)|^4375 ≤ (8774535318143/25000000000000 : ℝ)^3351
        have hw : |(2242247881/5000000000 : ℝ)|=(2242247881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068847933/5000000000 : ℝ)|^4375 ≤ (31597118977327/100000000000000 : ℝ)^3351
        have hw : |(2068847933/5000000000 : ℝ)|=(2068847933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (9058250376883429/100000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^2187 ≤ (9058250376883429/100000000000000000000 : ℝ)^512 := by
      have hnat : (11311 : ℕ)^2187*100000000000000000000^512 ≤ 9058250376883429^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 9058250376883429 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (9058250376883429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (2187/512 : ℝ) ≤ (28151925361643521/100000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^2187 ≤ (28151925361643521/100000000000000000000 : ℝ)^512 := by
      have hnat : (59 : ℕ)^2187*100000000000000000000^512 ≤ 28151925361643521^512*400^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 28151925361643521 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (28151925361643521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009058250376883429/50000000000000000000 : ℝ) ≤ (10000424097162577/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50009058250376883429/50000000000000000000 : ℝ)^512 ≤ (10000424097162577/10000000000000000 : ℝ)^2187 := by
      have hnat : (50009058250376883429 : ℕ)^512*10000000000000000^2187 ≤ 10000424097162577^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009058250376883429 50000000000000000000 10000424097162577 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424097162577/10000000000000000 : ℝ)) (X := (50009058250376883429/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000744203514770539/2000000000000000000 : ℝ) ≤ (10000871005753321/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (2000744203514770539/2000000000000000000 : ℝ)^512 ≤ (10000871005753321/10000000000000000 : ℝ)^2187 := by
      have hnat : (2000744203514770539 : ℕ)^512*10000000000000000^2187 ≤ 10000871005753321^2187*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000744203514770539 2000000000000000000 10000871005753321 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000871005753321/10000000000000000 : ℝ)) (X := (2000744203514770539/2000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028151925361643521/50000000000000000000 : ℝ) ≤ (2000263582868813/2000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50028151925361643521/50000000000000000000 : ℝ)^512 ≤ (2000263582868813/2000000000000000 : ℝ)^2187 := by
      have hnat : (50028151925361643521 : ℕ)^512*2000000000000000^2187 ≤ 2000263582868813^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028151925361643521 50000000000000000000 2000263582868813 2000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000263582868813/2000000000000000 : ℝ)) (X := (50028151925361643521/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9058250376883429/100000000000000000000 : ℝ) ≤ ((361908931621076753/362000000000000000 : ℝ)+2*(2940188097/2262500000000 : ℝ)*(11311/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (361908931621076753/362000000000000000 : ℝ)+2*(2940188097/2262500000000 : ℝ)*(11311/100000 : ℝ)=(10000424097162577/10000000000000000 : ℝ) by norm_num, show 1+2*(9058250376883429/100000000000000000000 : ℝ)=(50009058250376883429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28151925361643521/100000000000000000000 : ℝ)+(9058250376883429/100000000000000000000 : ℝ) ≤ ((361908931621076753/362000000000000000 : ℝ)+(2940188097/2262500000000 : ℝ)*((59/400 : ℝ)+(11311/100000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (361908931621076753/362000000000000000 : ℝ)+(2940188097/2262500000000 : ℝ)*((59/400 : ℝ)+(11311/100000 : ℝ))=(10000871005753321/10000000000000000 : ℝ) by norm_num, show 1+(28151925361643521/100000000000000000000 : ℝ)+(9058250376883429/100000000000000000000 : ℝ)=(2000744203514770539/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28151925361643521/100000000000000000000 : ℝ) ≤ ((361908931621076753/362000000000000000 : ℝ)+2*(2940188097/2262500000000 : ℝ)*(59/400 : ℝ))^(2187/512 : ℝ) := by
    rw [show (361908931621076753/362000000000000000 : ℝ)+2*(2940188097/2262500000000 : ℝ)*(59/400 : ℝ)=(2000263582868813/2000000000000000 : ℝ) by norm_num, show 1+2*(28151925361643521/100000000000000000000 : ℝ)=(50028151925361643521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (361908931621076753/362000000000000000 : ℝ)*(X 1 0+X 2 0)+(2940188097/2262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (361908931621076753/362000000000000000 : ℝ)) (alpha := (2940188097/2262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (361908931621076753/362000000000000000 : ℝ)*(X 0 1+X 2 1)+(2940188097/2262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (361908931621076753/362000000000000000 : ℝ)) (alpha := (2940188097/2262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (361908931621076753/362000000000000000 : ℝ)*(X 0 2+X 1 2)+(2940188097/2262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (361908931621076753/362000000000000000 : ℝ)) (alpha := (2940188097/2262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347611793/10000000000 : ℝ)*X 2 0+(5246609401/10000000000 : ℝ)*X 2 1+(-2065189539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-991279531/5000000000 : ℝ)*X 0 0+(655899241/1250000000 : ℝ)*X 0 1+(338020507/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1061095007/2000000000 : ℝ)*X 1 0+(-1903470889/10000000000 : ℝ)*X 1 1+(54083281/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652737537/5000000000 : ℝ)*X 2 0+(676041009/1250000000 : ℝ)*X 2 1+(-1903470873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4307912913/10000000000 : ℝ)*X 0 0+(2242247881/5000000000 : ℝ)*X 0 1+(2068847933/5000000000 : ℝ)*X 0 2+(4307912913/10000000000 : ℝ)*X 1 0+(2242247881/5000000000 : ℝ)*X 1 1+(2068847933/5000000000 : ℝ)*X 1 2+(4307912913/10000000000 : ℝ)*X 2 0+(2242247881/5000000000 : ℝ)*X 2 1+(2068847933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22016820834417008114998281/4525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840528077/100000000000000 : ℝ)*(base19) + (992113829/100000000000000 : ℝ)*(base23) + (34452709/12500000000000 : ℝ)*(lower1) + (2571851/2500000000000 : ℝ)*(upper3) + (11279453/25000000000000 : ℝ)*(lower4) + (103679547/100000000000000 : ℝ)*(upper5) + (1136186177562941/25000000000000 : ℝ)*(major0) + (1136186177562941/25000000000000 : ℝ)*(major1) + (1136186177562941/25000000000000 : ℝ)*(major2) + (658705401/25000000000000 : ℝ)*(sp0) + (6205990131018299/100000000000000 : ℝ)*(sp1) + (6205989290490223/100000000000000 : ℝ)*(sp2) + (6205986504082867/100000000000000 : ℝ)*(sp3) + (2883499127298679/100000000000000 : ℝ)*(sp4) + (2883499127298679/100000000000000 : ℝ)*(f.failure) + (6205990131018299/100000000000000 : ℝ)*(f.sum) + (3058919657181/905000000000000000000000000 : ℝ)*base66 + (84997365199769427/9050000000000000000000000000000 : ℝ)*base68 + (110586749330630573/9050000000000000000000000000000 : ℝ)*base69 + (133507302149130573/9050000000000000000000000000000 : ℝ)*base71 + (233095888209/905000000000000000000000000 : ℝ)*base73 + (1302643556217969427/9050000000000000000000000000000 : ℝ)*base76 + (33392126707880573/9050000000000000000000000000000 : ℝ)*base77 + (34960808738430573/9050000000000000000000000000000 : ℝ)*base79 + (4978329976729/905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (56338261/10000000000000000000000 : ℝ)*base90 + (56338261/10000000000000000000000 : ℝ)*base92 + (56338261/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1415_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s8_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982550613/10000000000 : ℝ)*x 0 + (2704457579/5000000000 : ℝ)*x 1 + (5246607687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982550613/10000000000 : ℝ)^4375 ≤ (6045605250279/50000000000000 : ℝ)^3351 := by
    have hnat : (1982550613 : ℕ)^4375*50000000000000^3351 ≤ 6045605250279^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982550613 10000000000 6045605250279 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704457579/5000000000 : ℝ)^4375 ≤ (8965692868179/20000000000000 : ℝ)^3351 := by
    have hnat : (2704457579 : ℕ)^4375*20000000000000^3351 ≤ 8965692868179^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704457579 5000000000 8965692868179 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246607687/10000000000 : ℝ)^4375 ≤ (8616065028573/20000000000000 : ℝ)^3351 := by
    have hnat : (5246607687 : ℕ)^4375*20000000000000^3351 ≤ 8616065028573^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246607687 10000000000 8616065028573 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982550613/10000000000 : ℝ), (2704457579/5000000000 : ℝ), (5246607687/10000000000 : ℝ)] ![(6045605250279/50000000000000 : ℝ), (8965692868179/20000000000000 : ℝ), (8616065028573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982550613/10000000000 : ℝ)|^4375 ≤ (6045605250279/50000000000000 : ℝ)^3351
        have hw : |(-1982550613/10000000000 : ℝ)|=(1982550613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704457579/5000000000 : ℝ)|^4375 ≤ (8965692868179/20000000000000 : ℝ)^3351
        have hw : |(2704457579/5000000000 : ℝ)|=(2704457579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246607687/10000000000 : ℝ)|^4375 ≤ (8616065028573/20000000000000 : ℝ)^3351
        have hw : |(5246607687/10000000000 : ℝ)|=(5246607687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347607433/10000000000 : ℝ)*x 0 + (-2065188501/10000000000 : ℝ)*x 1 + (655826821/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347607433/10000000000 : ℝ)^4375 ≤ (4416623599193/10000000000000 : ℝ)^3351 := by
    have hnat : (5347607433 : ℕ)^4375*10000000000000^3351 ≤ 4416623599193^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347607433 10000000000 4416623599193 10000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065188501/10000000000 : ℝ)^4375 ≤ (12753365093683/100000000000000 : ℝ)^3351 := by
    have hnat : (2065188501 : ℕ)^4375*100000000000000^3351 ≤ 12753365093683^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065188501 10000000000 12753365093683 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655826821/1250000000 : ℝ)^4375 ≤ (21540199454383/50000000000000 : ℝ)^3351 := by
    have hnat : (655826821 : ℕ)^4375*50000000000000^3351 ≤ 21540199454383^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655826821 1250000000 21540199454383 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347607433/10000000000 : ℝ), (-2065188501/10000000000 : ℝ), (655826821/1250000000 : ℝ)] ![(4416623599193/10000000000000 : ℝ), (12753365093683/100000000000000 : ℝ), (21540199454383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347607433/10000000000 : ℝ)|^4375 ≤ (4416623599193/10000000000000 : ℝ)^3351
        have hw : |(5347607433/10000000000 : ℝ)|=(5347607433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065188501/10000000000 : ℝ)|^4375 ≤ (12753365093683/100000000000000 : ℝ)^3351
        have hw : |(-2065188501/10000000000 : ℝ)|=(2065188501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655826821/1250000000 : ℝ)|^4375 ≤ (21540199454383/50000000000000 : ℝ)^3351
        have hw : |(655826821/1250000000 : ℝ)|=(655826821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673804051/5000000000 : ℝ)*x 0 + (5246614113/10000000000 : ℝ)*x 1 + (-2065188211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673804051/5000000000 : ℝ)^4375 ≤ (5520780400709/12500000000000 : ℝ)^3351 := by
    have hnat : (2673804051 : ℕ)^4375*12500000000000^3351 ≤ 5520780400709^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673804051 5000000000 5520780400709 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246614113/10000000000 : ℝ)^4375 ≤ (43080394031061/100000000000000 : ℝ)^3351 := by
    have hnat : (5246614113 : ℕ)^4375*100000000000000^3351 ≤ 43080394031061^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246614113 10000000000 43080394031061 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065188211/10000000000 : ℝ)^4375 ≤ (3188340688891/25000000000000 : ℝ)^3351 := by
    have hnat : (2065188211 : ℕ)^4375*25000000000000^3351 ≤ 3188340688891^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065188211 10000000000 3188340688891 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673804051/5000000000 : ℝ), (5246614113/10000000000 : ℝ), (-2065188211/10000000000 : ℝ)] ![(5520780400709/12500000000000 : ℝ), (43080394031061/100000000000000 : ℝ), (3188340688891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673804051/5000000000 : ℝ)|^4375 ≤ (5520780400709/12500000000000 : ℝ)^3351
        have hw : |(2673804051/5000000000 : ℝ)|=(2673804051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246614113/10000000000 : ℝ)|^4375 ≤ (43080394031061/100000000000000 : ℝ)^3351
        have hw : |(5246614113/10000000000 : ℝ)|=(5246614113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065188211/10000000000 : ℝ)|^4375 ≤ (3188340688891/25000000000000 : ℝ)^3351
        have hw : |(-2065188211/10000000000 : ℝ)|=(2065188211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307890049/10000000000 : ℝ)*x 0 + (4136440629/10000000000 : ℝ)*x 1 + (2242871489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307890049/10000000000 : ℝ)^4375 ≤ (16652254479017/50000000000000 : ℝ)^3351 := by
    have hnat : (4307890049 : ℕ)^4375*50000000000000^3351 ≤ 16652254479017^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307890049 10000000000 16652254479017 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136440629/10000000000 : ℝ)^4375 ≤ (15792302459861/50000000000000 : ℝ)^3351 := by
    have hnat : (4136440629 : ℕ)^4375*50000000000000^3351 ≤ 15792302459861^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136440629 10000000000 15792302459861 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242871489/5000000000 : ℝ)^4375 ≤ (3511088610871/10000000000000 : ℝ)^3351 := by
    have hnat : (2242871489 : ℕ)^4375*10000000000000^3351 ≤ 3511088610871^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242871489 5000000000 3511088610871 10000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307890049/10000000000 : ℝ), (4136440629/10000000000 : ℝ), (2242871489/5000000000 : ℝ)] ![(16652254479017/50000000000000 : ℝ), (15792302459861/50000000000000 : ℝ), (3511088610871/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307890049/10000000000 : ℝ)|^4375 ≤ (16652254479017/50000000000000 : ℝ)^3351
        have hw : |(4307890049/10000000000 : ℝ)|=(4307890049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136440629/10000000000 : ℝ)|^4375 ≤ (15792302459861/50000000000000 : ℝ)^3351
        have hw : |(4136440629/10000000000 : ℝ)|=(4136440629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242871489/5000000000 : ℝ)|^4375 ≤ (3511088610871/10000000000000 : ℝ)^3351
        have hw : |(2242871489/5000000000 : ℝ)|=(2242871489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982561743/10000000000 : ℝ)*x 0 + (1311799181/2500000000 : ℝ)*x 1 + (540832337/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982561743/10000000000 : ℝ)^4375 ≤ (6045649561597/50000000000000 : ℝ)^3351 := by
    have hnat : (1982561743 : ℕ)^4375*50000000000000^3351 ≤ 6045649561597^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982561743 10000000000 6045649561597 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311799181/2500000000 : ℝ)^4375 ≤ (10771659965489/25000000000000 : ℝ)^3351 := by
    have hnat : (1311799181 : ℕ)^4375*25000000000000^3351 ≤ 10771659965489^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311799181 2500000000 10771659965489 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540832337/1000000000 : ℝ)^4375 ≤ (44822061005997/100000000000000 : ℝ)^3351 := by
    have hnat : (540832337 : ℕ)^4375*100000000000000^3351 ≤ 44822061005997^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540832337 1000000000 44822061005997 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982561743/10000000000 : ℝ), (1311799181/2500000000 : ℝ), (540832337/1000000000 : ℝ)] ![(6045649561597/50000000000000 : ℝ), (10771659965489/25000000000000 : ℝ), (44822061005997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982561743/10000000000 : ℝ)|^4375 ≤ (6045649561597/50000000000000 : ℝ)^3351
        have hw : |(-1982561743/10000000000 : ℝ)|=(1982561743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311799181/2500000000 : ℝ)|^4375 ≤ (10771659965489/25000000000000 : ℝ)^3351
        have hw : |(1311799181/2500000000 : ℝ)|=(1311799181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540832337/1000000000 : ℝ)|^4375 ≤ (44822061005997/100000000000000 : ℝ)^3351
        have hw : |(540832337/1000000000 : ℝ)|=(540832337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153956513/5000000000 : ℝ)*x 0 + (896897523/2000000000 : ℝ)*x 1 + (4137704101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153956513/5000000000 : ℝ)^4375 ≤ (6660948175343/20000000000000 : ℝ)^3351 := by
    have hnat : (2153956513 : ℕ)^4375*20000000000000^3351 ≤ 6660948175343^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153956513 5000000000 6660948175343 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896897523/2000000000 : ℝ)^4375 ≤ (8774514506243/25000000000000 : ℝ)^3351 := by
    have hnat : (896897523 : ℕ)^4375*25000000000000^3351 ≤ 8774514506243^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896897523 2000000000 8774514506243 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137704101/10000000000 : ℝ)^4375 ≤ (61713283359/195312500000 : ℝ)^3351 := by
    have hnat : (4137704101 : ℕ)^4375*195312500000^3351 ≤ 61713283359^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137704101 10000000000 61713283359 195312500000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153956513/5000000000 : ℝ), (896897523/2000000000 : ℝ), (4137704101/10000000000 : ℝ)] ![(6660948175343/20000000000000 : ℝ), (8774514506243/25000000000000 : ℝ), (61713283359/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153956513/5000000000 : ℝ)|^4375 ≤ (6660948175343/20000000000000 : ℝ)^3351
        have hw : |(2153956513/5000000000 : ℝ)|=(2153956513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896897523/2000000000 : ℝ)|^4375 ≤ (8774514506243/25000000000000 : ℝ)^3351
        have hw : |(896897523/2000000000 : ℝ)|=(896897523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137704101/10000000000 : ℝ)|^4375 ≤ (61713283359/195312500000 : ℝ)^3351
        have hw : |(4137704101/10000000000 : ℝ)|=(4137704101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83569097/100000000 : ℝ)*x 0 + (-76203819/1250000000 : ℝ)*x 1 + (2723000891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83569097/100000000 : ℝ)^4375 ≤ (1977718212871/2500000000000 : ℝ)^3351 := by
    have hnat : (83569097 : ℕ)^4375*2500000000000^3351 ≤ 1977718212871^3351*100000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83569097 100000000 1977718212871 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76203819/1250000000 : ℝ)^4375 ≤ (1296513080651/50000000000000 : ℝ)^3351 := by
    have hnat : (76203819 : ℕ)^4375*50000000000000^3351 ≤ 1296513080651^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76203819 1250000000 1296513080651 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723000891/10000000000 : ℝ)^4375 ≤ (3659649063461/20000000000000 : ℝ)^3351 := by
    have hnat : (2723000891 : ℕ)^4375*20000000000000^3351 ≤ 3659649063461^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723000891 10000000000 3659649063461 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83569097/100000000 : ℝ), (-76203819/1250000000 : ℝ), (2723000891/10000000000 : ℝ)] ![(1977718212871/2500000000000 : ℝ), (1296513080651/50000000000000 : ℝ), (3659649063461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83569097/100000000 : ℝ)|^4375 ≤ (1977718212871/2500000000000 : ℝ)^3351
        have hw : |(83569097/100000000 : ℝ)|=(83569097/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76203819/1250000000 : ℝ)|^4375 ≤ (1296513080651/50000000000000 : ℝ)^3351
        have hw : |(-76203819/1250000000 : ℝ)|=(76203819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723000891/10000000000 : ℝ)|^4375 ≤ (3659649063461/20000000000000 : ℝ)^3351
        have hw : |(2723000891/10000000000 : ℝ)|=(2723000891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s8_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1676062493/2000000000 : ℝ)*x 0 + (130459203/500000000 : ℝ)*x 1 + (-91569531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1676062493/2000000000 : ℝ)^4375 ≤ (79398086292197/100000000000000 : ℝ)^3351 := by
    have hnat : (1676062493 : ℕ)^4375*100000000000000^3351 ≤ 79398086292197^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676062493 2000000000 79398086292197 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130459203/500000000 : ℝ)^4375 ≤ (17306130757657/100000000000000 : ℝ)^3351 := by
    have hnat : (130459203 : ℕ)^4375*100000000000000^3351 ≤ 17306130757657^3351*500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130459203 500000000 17306130757657 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91569531/1250000000 : ℝ)^4375 ≤ (3295782940909/100000000000000 : ℝ)^3351 := by
    have hnat : (91569531 : ℕ)^4375*100000000000000^3351 ≤ 3295782940909^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91569531 1250000000 3295782940909 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1676062493/2000000000 : ℝ), (130459203/500000000 : ℝ), (-91569531/1250000000 : ℝ)] ![(79398086292197/100000000000000 : ℝ), (17306130757657/100000000000000 : ℝ), (3295782940909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1676062493/2000000000 : ℝ)|^4375 ≤ (79398086292197/100000000000000 : ℝ)^3351
        have hw : |(1676062493/2000000000 : ℝ)|=(1676062493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130459203/500000000 : ℝ)|^4375 ≤ (17306130757657/100000000000000 : ℝ)^3351
        have hw : |(130459203/500000000 : ℝ)|=(130459203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91569531/1250000000 : ℝ)|^4375 ≤ (3295782940909/100000000000000 : ℝ)^3351
        have hw : |(-91569531/1250000000 : ℝ)|=(91569531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (9058250376883429/100000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^2187 ≤ (9058250376883429/100000000000000000000 : ℝ)^512 := by
      have hnat : (11311 : ℕ)^2187*100000000000000000000^512 ≤ 9058250376883429^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 9058250376883429 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (9058250376883429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (1758985855549843/6250000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^2187 ≤ (1758985855549843/6250000000000000000 : ℝ)^512 := by
      have hnat : (14749 : ℕ)^2187*6250000000000000000^512 ≤ 1758985855549843^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 1758985855549843 6250000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (1758985855549843/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009058250376883429/50000000000000000000 : ℝ) ≤ (10000424097162577/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50009058250376883429/50000000000000000000 : ℝ)^512 ≤ (10000424097162577/10000000000000000 : ℝ)^2187 := by
      have hnat : (50009058250376883429 : ℕ)^512*10000000000000000^2187 ≤ 10000424097162577^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009058250376883429 50000000000000000000 10000424097162577 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424097162577/10000000000000000 : ℝ)) (X := (50009058250376883429/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037202024065680917/100000000000000000000 : ℝ) ≤ (5000435407484169/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (100037202024065680917/100000000000000000000 : ℝ)^512 ≤ (5000435407484169/5000000000000000 : ℝ)^2187 := by
      have hnat : (100037202024065680917 : ℕ)^512*5000000000000000^2187 ≤ 5000435407484169^2187*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037202024065680917 100000000000000000000 5000435407484169 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000435407484169/5000000000000000 : ℝ)) (X := (100037202024065680917/100000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126758985855549843/3125000000000000000 : ℝ) ≤ (10001317532774099/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (3126758985855549843/3125000000000000000 : ℝ)^512 ≤ (10001317532774099/10000000000000000 : ℝ)^2187 := by
      have hnat : (3126758985855549843 : ℕ)^512*10000000000000000^2187 ≤ 10001317532774099^2187*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126758985855549843 3125000000000000000 10001317532774099 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001317532774099/10000000000000000 : ℝ)) (X := (3126758985855549843/3125000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9058250376883429/100000000000000000000 : ℝ) ≤ ((2148209524740188399/2148750000000000000 : ℝ)+2*(446717805761/343800000000000 : ℝ)*(11311/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (2148209524740188399/2148750000000000000 : ℝ)+2*(446717805761/343800000000000 : ℝ)*(11311/100000 : ℝ)=(10000424097162577/10000000000000000 : ℝ) by norm_num, show 1+2*(9058250376883429/100000000000000000000 : ℝ)=(50009058250376883429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1758985855549843/6250000000000000000 : ℝ)+(9058250376883429/100000000000000000000 : ℝ) ≤ ((2148209524740188399/2148750000000000000 : ℝ)+(446717805761/343800000000000 : ℝ)*((14749/100000 : ℝ)+(11311/100000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (2148209524740188399/2148750000000000000 : ℝ)+(446717805761/343800000000000 : ℝ)*((14749/100000 : ℝ)+(11311/100000 : ℝ))=(5000435407484169/5000000000000000 : ℝ) by norm_num, show 1+(1758985855549843/6250000000000000000 : ℝ)+(9058250376883429/100000000000000000000 : ℝ)=(100037202024065680917/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1758985855549843/6250000000000000000 : ℝ) ≤ ((2148209524740188399/2148750000000000000 : ℝ)+2*(446717805761/343800000000000 : ℝ)*(14749/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (2148209524740188399/2148750000000000000 : ℝ)+2*(446717805761/343800000000000 : ℝ)*(14749/100000 : ℝ)=(10001317532774099/10000000000000000 : ℝ) by norm_num, show 1+2*(1758985855549843/6250000000000000000 : ℝ)=(3126758985855549843/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2148209524740188399/2148750000000000000 : ℝ)*(X 1 0+X 2 0)+(446717805761/343800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (2148209524740188399/2148750000000000000 : ℝ)) (alpha := (446717805761/343800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2148209524740188399/2148750000000000000 : ℝ)*(X 0 1+X 2 1)+(446717805761/343800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (2148209524740188399/2148750000000000000 : ℝ)) (alpha := (446717805761/343800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2148209524740188399/2148750000000000000 : ℝ)*(X 0 2+X 1 2)+(446717805761/343800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (2148209524740188399/2148750000000000000 : ℝ)) (alpha := (446717805761/343800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1982550613/10000000000 : ℝ)*X 0 0+(2704457579/5000000000 : ℝ)*X 0 1+(5246607687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347607433/10000000000 : ℝ)*X 1 0+(-2065188501/10000000000 : ℝ)*X 1 1+(655826821/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673804051/5000000000 : ℝ)*X 2 0+(5246614113/10000000000 : ℝ)*X 2 1+(-2065188211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307890049/10000000000 : ℝ)*X 0 0+(4136440629/10000000000 : ℝ)*X 0 1+(2242871489/5000000000 : ℝ)*X 0 2+(4307890049/10000000000 : ℝ)*X 1 0+(4136440629/10000000000 : ℝ)*X 1 1+(2242871489/5000000000 : ℝ)*X 1 2+(4307890049/10000000000 : ℝ)*X 2 0+(4136440629/10000000000 : ℝ)*X 2 1+(2242871489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1982561743/10000000000 : ℝ)*X 0 0+(1311799181/2500000000 : ℝ)*X 0 1+(540832337/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2153956513/5000000000 : ℝ)*X 0 0+(896897523/2000000000 : ℝ)*X 0 1+(4137704101/10000000000 : ℝ)*X 0 2+(2153956513/5000000000 : ℝ)*X 1 0+(896897523/2000000000 : ℝ)*X 1 1+(4137704101/10000000000 : ℝ)*X 1 2+(2153956513/5000000000 : ℝ)*X 2 0+(896897523/2000000000 : ℝ)*X 2 1+(4137704101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83569097/100000000 : ℝ)*X 1 0+(-76203819/1250000000 : ℝ)*X 1 1+(2723000891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_6 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1676062493/2000000000 : ℝ)*X 2 0+(130459203/500000000 : ℝ)*X 2 1+(-91569531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s8_7 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1946018300441019905743469/1193750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (280468723/100000000000000 : ℝ)*(lower2) + (97925671/25000000000000 : ℝ)*(upper3) + (311253807/100000000000000 : ℝ)*(upper5) + (4512191235640143/100000000000000 : ℝ)*(major0) + (4512191235640143/100000000000000 : ℝ)*(major1) + (282011952227509/6250000000000 : ℝ)*(major2) + (3080668795264913/50000000000000 : ℝ)*(sp0) + (3080767507973421/50000000000000 : ℝ)*(sp1) + (616153546917127/10000000000000 : ℝ)*(sp2) + (715711183776051/25000000000000 : ℝ)*(sp3) + (99932992011/50000000000000 : ℝ)*(sp4) + (225323143/100000000000000 : ℝ)*(sp5) + (1220283503/50000000000000 : ℝ)*(sp6) + (993671289/50000000000000 : ℝ)*(sp7) + (1431422480213673/50000000000000 : ℝ)*(f.failure) + (6161537456513847/100000000000000 : ℝ)*(f.sum) + (371268236437993/34380000000000000000000000000 : ℝ)*base66 + (2572755077645673943/214875000000000000000000000000000 : ℝ)*base68 + (358734197616995897/107437500000000000000000000000000 : ℝ)*base70 + (1169715185690298943/214875000000000000000000000000000 : ℝ)*base72 + (19326161205253/34380000000000000000000000000 : ℝ)*base74 + (1187123520741995897/107437500000000000000000000000000 : ℝ)*base76 + (1219023388648601731/71625000000000000000000000000000 : ℝ)*base78 + (535901915607476731/71625000000000000000000000000000 : ℝ)*base80 + (10948632425011/5730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10996107/5000000000000000000000 : ℝ)*base90 + (10996107/5000000000000000000000 : ℝ)*base92 + (60996107/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1415_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1415_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1415_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1415_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1415_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
