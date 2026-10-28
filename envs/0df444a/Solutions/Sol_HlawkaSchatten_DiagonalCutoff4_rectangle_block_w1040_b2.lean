-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:35.732079+00:00
-- url     : https://prove2.me/submissions/ac4c3e53-458a-45af-a7e6-275907ebe281

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
theorem support_rectangle_w1040_s6_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88663221/400000000 : ℝ)*x 0 + (1348862099/2500000000 : ℝ)*x 1 + (5263360169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88663221/400000000 : ℝ)^8233 ≤ (2691868383911/20000000000000 : ℝ)^6185 := by
    have hnat : (88663221 : ℕ)^8233*20000000000000^6185 ≤ 2691868383911^6185*400000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88663221 400000000 2691868383911 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348862099/2500000000 : ℝ)^8233 ≤ (21992040151077/50000000000000 : ℝ)^6185 := by
    have hnat : (1348862099 : ℕ)^8233*50000000000000^6185 ≤ 21992040151077^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348862099 2500000000 21992040151077 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263360169/10000000000 : ℝ)^8233 ≤ (42556577752297/100000000000000 : ℝ)^6185 := by
    have hnat : (5263360169 : ℕ)^8233*100000000000000^6185 ≤ 42556577752297^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263360169 10000000000 42556577752297 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88663221/400000000 : ℝ), (1348862099/2500000000 : ℝ), (5263360169/10000000000 : ℝ)] ![(2691868383911/20000000000000 : ℝ), (21992040151077/50000000000000 : ℝ), (42556577752297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88663221/400000000 : ℝ)|^8233 ≤ (2691868383911/20000000000000 : ℝ)^6185
        have hw : |(-88663221/400000000 : ℝ)|=(88663221/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348862099/2500000000 : ℝ)|^8233 ≤ (21992040151077/50000000000000 : ℝ)^6185
        have hw : |(1348862099/2500000000 : ℝ)|=(1348862099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263360169/10000000000 : ℝ)|^8233 ≤ (42556577752297/100000000000000 : ℝ)^6185
        have hw : |(5263360169/10000000000 : ℝ)|=(5263360169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672595921/5000000000 : ℝ)*x 0 + (-570903597/2500000000 : ℝ)*x 1 + (1315840037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672595921/5000000000 : ℝ)^8233 ≤ (21719784167287/50000000000000 : ℝ)^6185 := by
    have hnat : (2672595921 : ℕ)^8233*50000000000000^6185 ≤ 21719784167287^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672595921 5000000000 21719784167287 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570903597/2500000000 : ℝ)^8233 ≤ (700192706157/5000000000000 : ℝ)^6185 := by
    have hnat : (570903597 : ℕ)^8233*5000000000000^6185 ≤ 700192706157^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570903597 2500000000 700192706157 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315840037/2500000000 : ℝ)^8233 ≤ (42556577526279/100000000000000 : ℝ)^6185 := by
    have hnat : (1315840037 : ℕ)^8233*100000000000000^6185 ≤ 42556577526279^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315840037 2500000000 42556577526279 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672595921/5000000000 : ℝ), (-570903597/2500000000 : ℝ), (1315840037/2500000000 : ℝ)] ![(21719784167287/50000000000000 : ℝ), (700192706157/5000000000000 : ℝ), (42556577526279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672595921/5000000000 : ℝ)|^8233 ≤ (21719784167287/50000000000000 : ℝ)^6185
        have hw : |(2672595921/5000000000 : ℝ)|=(2672595921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-570903597/2500000000 : ℝ)|^8233 ≤ (700192706157/5000000000000 : ℝ)^6185
        have hw : |(-570903597/2500000000 : ℝ)|=(570903597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315840037/2500000000 : ℝ)|^8233 ≤ (42556577526279/100000000000000 : ℝ)^6185
        have hw : |(1315840037/2500000000 : ℝ)|=(1315840037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345191699/10000000000 : ℝ)*x 0 + (21053441/40000000 : ℝ)*x 1 + (-1141807221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345191699/10000000000 : ℝ)^8233 ≤ (43439566787623/100000000000000 : ℝ)^6185 := by
    have hnat : (5345191699 : ℕ)^8233*100000000000000^6185 ≤ 43439566787623^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345191699 10000000000 43439566787623 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21053441/40000000 : ℝ)^8233 ≤ (42556578624077/100000000000000 : ℝ)^6185 := by
    have hnat : (21053441 : ℕ)^8233*100000000000000^6185 ≤ 42556578624077^6185*40000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21053441 40000000 42556578624077 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141807221/5000000000 : ℝ)^8233 ≤ (2800770912787/20000000000000 : ℝ)^6185 := by
    have hnat : (1141807221 : ℕ)^8233*20000000000000^6185 ≤ 2800770912787^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141807221 5000000000 2800770912787 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345191699/10000000000 : ℝ), (21053441/40000000 : ℝ), (-1141807221/5000000000 : ℝ)] ![(43439566787623/100000000000000 : ℝ), (42556578624077/100000000000000 : ℝ), (2800770912787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345191699/10000000000 : ℝ)|^8233 ≤ (43439566787623/100000000000000 : ℝ)^6185
        have hw : |(5345191699/10000000000 : ℝ)|=(5345191699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21053441/40000000 : ℝ)|^8233 ≤ (42556578624077/100000000000000 : ℝ)^6185
        have hw : |(21053441/40000000 : ℝ)|=(21053441/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141807221/5000000000 : ℝ)|^8233 ≤ (2800770912787/20000000000000 : ℝ)^6185
        have hw : |(-1141807221/5000000000 : ℝ)|=(1141807221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094803209/2500000000 : ℝ)*x 0 + (106309327/250000000 : ℝ)*x 1 + (1127478077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094803209/2500000000 : ℝ)^8233 ≤ (33316072015943/100000000000000 : ℝ)^6185 := by
    have hnat : (1094803209 : ℕ)^8233*100000000000000^6185 ≤ 33316072015943^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094803209 2500000000 33316072015943 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106309327/250000000 : ℝ)^8233 ≤ (32037779434031/100000000000000 : ℝ)^6185 := by
    have hnat : (106309327 : ℕ)^8233*100000000000000^6185 ≤ 32037779434031^6185*250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106309327 250000000 32037779434031 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127478077/2500000000 : ℝ)^8233 ≤ (34646148536531/100000000000000 : ℝ)^6185 := by
    have hnat : (1127478077 : ℕ)^8233*100000000000000^6185 ≤ 34646148536531^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127478077 2500000000 34646148536531 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094803209/2500000000 : ℝ), (106309327/250000000 : ℝ), (1127478077/2500000000 : ℝ)] ![(33316072015943/100000000000000 : ℝ), (32037779434031/100000000000000 : ℝ), (34646148536531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094803209/2500000000 : ℝ)|^8233 ≤ (33316072015943/100000000000000 : ℝ)^6185
        have hw : |(1094803209/2500000000 : ℝ)|=(1094803209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(106309327/250000000 : ℝ)|^8233 ≤ (32037779434031/100000000000000 : ℝ)^6185
        have hw : |(106309327/250000000 : ℝ)|=(106309327/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127478077/2500000000 : ℝ)|^8233 ≤ (34646148536531/100000000000000 : ℝ)^6185
        have hw : |(1127478077/2500000000 : ℝ)|=(1127478077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108292883/5000000000 : ℝ)*x 0 + (5263693843/10000000000 : ℝ)*x 1 + (5395113539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108292883/5000000000 : ℝ)^8233 ≤ (13459384281223/100000000000000 : ℝ)^6185 := by
    have hnat : (1108292883 : ℕ)^8233*100000000000000^6185 ≤ 13459384281223^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108292883 5000000000 13459384281223 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263693843/10000000000 : ℝ)^8233 ≤ (21280084514813/50000000000000 : ℝ)^6185 := by
    have hnat : (5263693843 : ℕ)^8233*50000000000000^6185 ≤ 21280084514813^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263693843 10000000000 21280084514813 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395113539/10000000000 : ℝ)^8233 ≤ (43980446667129/100000000000000 : ℝ)^6185 := by
    have hnat : (5395113539 : ℕ)^8233*100000000000000^6185 ≤ 43980446667129^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395113539 10000000000 43980446667129 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108292883/5000000000 : ℝ), (5263693843/10000000000 : ℝ), (5395113539/10000000000 : ℝ)] ![(13459384281223/100000000000000 : ℝ), (21280084514813/50000000000000 : ℝ), (43980446667129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108292883/5000000000 : ℝ)|^8233 ≤ (13459384281223/100000000000000 : ℝ)^6185
        have hw : |(-1108292883/5000000000 : ℝ)|=(1108292883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263693843/10000000000 : ℝ)|^8233 ≤ (21280084514813/50000000000000 : ℝ)^6185
        have hw : |(5263693843/10000000000 : ℝ)|=(5263693843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395113539/10000000000 : ℝ)|^8233 ≤ (43980446667129/100000000000000 : ℝ)^6185
        have hw : |(5395113539/10000000000 : ℝ)|=(5395113539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311991003/10000000000 : ℝ)*x 0 + (-2151861063/10000000000 : ℝ)*x 1 + (1348778383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311991003/10000000000 : ℝ)^8233 ≤ (5385097097517/12500000000000 : ℝ)^6185 := by
    have hnat : (5311991003 : ℕ)^8233*12500000000000^6185 ≤ 5385097097517^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311991003 10000000000 5385097097517 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151861063/10000000000 : ℝ)^8233 ≤ (6469388304143/50000000000000 : ℝ)^6185 := by
    have hnat : (2151861063 : ℕ)^8233*50000000000000^6185 ≤ 6469388304143^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151861063 10000000000 6469388304143 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348778383/2500000000 : ℝ)^8233 ≤ (4398044659117/10000000000000 : ℝ)^6185 := by
    have hnat : (1348778383 : ℕ)^8233*10000000000000^6185 ≤ 4398044659117^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348778383 2500000000 4398044659117 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311991003/10000000000 : ℝ), (-2151861063/10000000000 : ℝ), (1348778383/2500000000 : ℝ)] ![(5385097097517/12500000000000 : ℝ), (6469388304143/50000000000000 : ℝ), (4398044659117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311991003/10000000000 : ℝ)|^8233 ≤ (5385097097517/12500000000000 : ℝ)^6185
        have hw : |(5311991003/10000000000 : ℝ)|=(5311991003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151861063/10000000000 : ℝ)|^8233 ≤ (6469388304143/50000000000000 : ℝ)^6185
        have hw : |(-2151861063/10000000000 : ℝ)|=(2151861063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348778383/2500000000 : ℝ)|^8233 ≤ (4398044659117/10000000000000 : ℝ)^6185
        have hw : |(1348778383/2500000000 : ℝ)|=(1348778383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311991001/10000000000 : ℝ)*x 0 + (5395113541/10000000000 : ℝ)*x 1 + (-1075930527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311991001/10000000000 : ℝ)^8233 ≤ (8616155351709/20000000000000 : ℝ)^6185 := by
    have hnat : (5311991001 : ℕ)^8233*20000000000000^6185 ≤ 8616155351709^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311991001 10000000000 8616155351709 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395113541/10000000000 : ℝ)^8233 ≤ (43980446688831/100000000000000 : ℝ)^6185 := by
    have hnat : (5395113541 : ℕ)^8233*100000000000000^6185 ≤ 43980446688831^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395113541 10000000000 43980446688831 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075930527/5000000000 : ℝ)^8233 ≤ (12938776536251/100000000000000 : ℝ)^6185 := by
    have hnat : (1075930527 : ℕ)^8233*100000000000000^6185 ≤ 12938776536251^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075930527 5000000000 12938776536251 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311991001/10000000000 : ℝ), (5395113541/10000000000 : ℝ), (-1075930527/5000000000 : ℝ)] ![(8616155351709/20000000000000 : ℝ), (43980446688831/100000000000000 : ℝ), (12938776536251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311991001/10000000000 : ℝ)|^8233 ≤ (8616155351709/20000000000000 : ℝ)^6185
        have hw : |(5311991001/10000000000 : ℝ)|=(5311991001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395113541/10000000000 : ℝ)|^8233 ≤ (43980446688831/100000000000000 : ℝ)^6185
        have hw : |(5395113541/10000000000 : ℝ)|=(5395113541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075930527/5000000000 : ℝ)|^8233 ≤ (12938776536251/100000000000000 : ℝ)^6185
        have hw : |(-1075930527/5000000000 : ℝ)|=(1075930527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s6_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379223099/10000000000 : ℝ)*x 0 + (35228607/78125000 : ℝ)*x 1 + (4253026087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379223099/10000000000 : ℝ)^8233 ≤ (33316175948269/100000000000000 : ℝ)^6185 := by
    have hnat : (4379223099 : ℕ)^8233*100000000000000^6185 ≤ 33316175948269^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379223099 10000000000 33316175948269 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35228607/78125000 : ℝ)^8233 ≤ (6927899108993/20000000000000 : ℝ)^6185 := by
    have hnat : (35228607 : ℕ)^8233*20000000000000^6185 ≤ 6927899108993^6185*78125000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35228607 78125000 6927899108993 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253026087/10000000000 : ℝ)^8233 ≤ (6408865696897/20000000000000 : ℝ)^6185 := by
    have hnat : (4253026087 : ℕ)^8233*20000000000000^6185 ≤ 6408865696897^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253026087 10000000000 6408865696897 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379223099/10000000000 : ℝ), (35228607/78125000 : ℝ), (4253026087/10000000000 : ℝ)] ![(33316175948269/100000000000000 : ℝ), (6927899108993/20000000000000 : ℝ), (6408865696897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379223099/10000000000 : ℝ)|^8233 ≤ (33316175948269/100000000000000 : ℝ)^6185
        have hw : |(4379223099/10000000000 : ℝ)|=(4379223099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35228607/78125000 : ℝ)|^8233 ≤ (6927899108993/20000000000000 : ℝ)^6185
        have hw : |(35228607/78125000 : ℝ)|=(35228607/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253026087/10000000000 : ℝ)|^8233 ≤ (6408865696897/20000000000000 : ℝ)^6185
        have hw : |(4253026087/10000000000 : ℝ)|=(4253026087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7/50 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/25000 : ℝ) ^ (1029/256 : ℝ) ≤ (14839889696186867/100000000000000000000 : ℝ) := by
    have hpowers : (2789/25000 : ℝ)^1029 ≤ (14839889696186867/100000000000000000000 : ℝ)^256 := by
      have hnat : (2789 : ℕ)^1029*100000000000000000000^256 ≤ 14839889696186867^256*25000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 25000 14839889696186867 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/25000 : ℝ)) (X := (14839889696186867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (1029/256 : ℝ) ≤ (37480885259725911/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^1029 ≤ (37480885259725911/100000000000000000000 : ℝ)^256 := by
      have hnat : (439 : ℕ)^1029*100000000000000000000^256 ≤ 37480885259725911^256*3125^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 37480885259725911 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (37480885259725911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014839889696186867/50000000000000000000 : ℝ) ≤ (1250092288346061/1250000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50014839889696186867/50000000000000000000 : ℝ)^256 ≤ (1250092288346061/1250000000000000 : ℝ)^1029 := by
      have hnat : (50014839889696186867 : ℕ)^256*1250000000000000^1029 ≤ 1250092288346061^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014839889696186867 50000000000000000000 1250092288346061 1250000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250092288346061/1250000000000000 : ℝ)) (X := (50014839889696186867/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026160387477956389/50000000000000000000 : ℝ) ≤ (2500325351967223/2500000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50026160387477956389/50000000000000000000 : ℝ)^256 ≤ (2500325351967223/2500000000000000 : ℝ)^1029 := by
      have hnat : (50026160387477956389 : ℕ)^256*2500000000000000^1029 ≤ 2500325351967223^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026160387477956389 50000000000000000000 2500325351967223 2500000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500325351967223/2500000000000000 : ℝ)) (X := (50026160387477956389/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037480885259725911/50000000000000000000 : ℝ) ≤ (625116531810581/625000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50037480885259725911/50000000000000000000 : ℝ)^256 ≤ (625116531810581/625000000000000 : ℝ)^1029 := by
      have hnat : (50037480885259725911 : ℕ)^256*625000000000000^1029 ≤ 625116531810581^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037480885259725911 50000000000000000000 625116531810581 625000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625116531810581/625000000000000 : ℝ)) (X := (50037480885259725911/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14839889696186867/100000000000000000000 : ℝ) ≤ ((451712051115972707/451875000000000000 : ℝ)+2*(140775275101/72300000000000 : ℝ)*(2789/25000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (451712051115972707/451875000000000000 : ℝ)+2*(140775275101/72300000000000 : ℝ)*(2789/25000 : ℝ)=(1250092288346061/1250000000000000 : ℝ) by norm_num, show 1+2*(14839889696186867/100000000000000000000 : ℝ)=(50014839889696186867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37480885259725911/100000000000000000000 : ℝ)+(14839889696186867/100000000000000000000 : ℝ) ≤ ((451712051115972707/451875000000000000 : ℝ)+(140775275101/72300000000000 : ℝ)*((439/3125 : ℝ)+(2789/25000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (451712051115972707/451875000000000000 : ℝ)+(140775275101/72300000000000 : ℝ)*((439/3125 : ℝ)+(2789/25000 : ℝ))=(2500325351967223/2500000000000000 : ℝ) by norm_num, show 1+(37480885259725911/100000000000000000000 : ℝ)+(14839889696186867/100000000000000000000 : ℝ)=(50026160387477956389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37480885259725911/100000000000000000000 : ℝ) ≤ ((451712051115972707/451875000000000000 : ℝ)+2*(140775275101/72300000000000 : ℝ)*(439/3125 : ℝ))^(1029/256 : ℝ) := by
    rw [show (451712051115972707/451875000000000000 : ℝ)+2*(140775275101/72300000000000 : ℝ)*(439/3125 : ℝ)=(625116531810581/625000000000000 : ℝ) by norm_num, show 1+2*(37480885259725911/100000000000000000000 : ℝ)=(50037480885259725911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (451712051115972707/451875000000000000 : ℝ)*(X 1 0+X 2 0)+(140775275101/72300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (451712051115972707/451875000000000000 : ℝ)) (alpha := (140775275101/72300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (451712051115972707/451875000000000000 : ℝ)*(X 0 1+X 2 1)+(140775275101/72300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (451712051115972707/451875000000000000 : ℝ)) (alpha := (140775275101/72300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (451712051115972707/451875000000000000 : ℝ)*(X 0 2+X 1 2)+(140775275101/72300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (451712051115972707/451875000000000000 : ℝ)) (alpha := (140775275101/72300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88663221/400000000 : ℝ)*X 0 0+(1348862099/2500000000 : ℝ)*X 0 1+(5263360169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672595921/5000000000 : ℝ)*X 1 0+(-570903597/2500000000 : ℝ)*X 1 1+(1315840037/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345191699/10000000000 : ℝ)*X 2 0+(21053441/40000000 : ℝ)*X 2 1+(-1141807221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094803209/2500000000 : ℝ)*X 0 0+(106309327/250000000 : ℝ)*X 0 1+(1127478077/2500000000 : ℝ)*X 0 2+(1094803209/2500000000 : ℝ)*X 1 0+(106309327/250000000 : ℝ)*X 1 1+(1127478077/2500000000 : ℝ)*X 1 2+(1094803209/2500000000 : ℝ)*X 2 0+(106309327/250000000 : ℝ)*X 2 1+(1127478077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1108292883/5000000000 : ℝ)*X 0 0+(5263693843/10000000000 : ℝ)*X 0 1+(5395113539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311991003/10000000000 : ℝ)*X 1 0+(-2151861063/10000000000 : ℝ)*X 1 1+(1348778383/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311991001/10000000000 : ℝ)*X 2 0+(5395113541/10000000000 : ℝ)*X 2 1+(-1075930527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379223099/10000000000 : ℝ)*X 0 0+(35228607/78125000 : ℝ)*X 0 1+(4253026087/10000000000 : ℝ)*X 0 2+(4379223099/10000000000 : ℝ)*X 1 0+(35228607/78125000 : ℝ)*X 1 1+(4253026087/10000000000 : ℝ)*X 1 2+(4379223099/10000000000 : ℝ)*X 2 0+(35228607/78125000 : ℝ)*X 2 1+(4253026087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4802298021527843626929/602500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1714266497/100000000000000 : ℝ)*(base19) + (1437627901/100000000000000 : ℝ)*(base23) + (19803201/50000000000000 : ℝ)*(lower2) + (26612469/10000000000000 : ℝ)*(upper3) + (875959/1000000000000 : ℝ)*(upper5) + (5726869928860473/100000000000000 : ℝ)*(major0) + (5726869928860473/100000000000000 : ℝ)*(major1) + (5726869928860473/100000000000000 : ℝ)*(major2) + (7570746887068029/100000000000000 : ℝ)*(sp0) + (7570785396665191/100000000000000 : ℝ)*(sp1) + (7570785673303787/100000000000000 : ℝ)*(sp2) + (388292653768797/10000000000000 : ℝ)*(sp3) + (2011193183/5000000000000 : ℝ)*(sp4) + (2594341397/10000000000000 : ℝ)*(sp7) + (3882952481101941/100000000000000 : ℝ)*(f.failure) + (946348388866461/12500000000000 : ℝ)*(f.sum) + (2032934328117/602500000000000000000000000 : ℝ)*base66 + (93455297985186113/15062500000000000000000000000000 : ℝ)*base68 + (122825901271876387/15062500000000000000000000000000 : ℝ)*base69 + (232405808941936113/15062500000000000000000000000000 : ℝ)*base72 + (3410222669869/1205000000000000000000000000 : ℝ)*base74 + (417746960702688887/15062500000000000000000000000000 : ℝ)*base75 + (160694636575123613/15062500000000000000000000000000 : ℝ)*base78 + (363753485606938887/15062500000000000000000000000000 : ℝ)*base79 + (8523487980911/1205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3425691/1000000000000000000000 : ℝ)*base89 + (3425691/1000000000000000000000 : ℝ)*base91 + (3425691/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25079361034893018804798701/3765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611978381/50000000000000 : ℝ)*(base19) + (332654827/25000000000000 : ℝ)*(base23) + (6673181/5000000000000 : ℝ)*(upper3) + (47131897/100000000000000 : ℝ)*(lower4) + (25019879/20000000000000 : ℝ)*(upper5) + (1438983268099483/25000000000000 : ℝ)*(major0) + (1438983268099483/25000000000000 : ℝ)*(major1) + (1438983268099483/25000000000000 : ℝ)*(major2) + (6448838193/20000000000000 : ℝ)*(sp1) + (35572267577/100000000000000 : ℝ)*(sp2) + (1521841589388593/20000000000000 : ℝ)*(sp4) + (1902293619698809/25000000000000 : ℝ)*(sp5) + (7609171044056079/100000000000000 : ℝ)*(sp6) + (487832246981281/12500000000000 : ℝ)*(sp7) + (487832246981281/12500000000000 : ℝ)*(f.failure) + (1521841589388593/20000000000000 : ℝ)*(f.sum) + (6584836823749/1807500000000000000000000000 : ℝ)*base66 + (1455717536791851/1882812500000000000000000000000 : ℝ)*base67 + (19203564540479351/1882812500000000000000000000000 : ℝ)*base69 + (11871051830349327/3765625000000000000000000000000 : ℝ)*base71 + (4171729166417/903750000000000000000000000 : ℝ)*base74 + (74741293610380577/3765625000000000000000000000000 : ℝ)*base75 + (21453742165911827/3765625000000000000000000000000 : ℝ)*base77 + (3030950277383/14709472656250000000000000000 : ℝ)*base80 + (2032874389799/451875000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (130031/125000000000000000000 : ℝ)*base89 + (130031/125000000000000000000 : ℝ)*base91 + (130031/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s7_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88665029/400000000 : ℝ)*x 0 + (674365869/1250000000 : ℝ)*x 1 + (105277039/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88665029/400000000 : ℝ)^8233 ≤ (6729853630367/50000000000000 : ℝ)^6185 := by
    have hnat : (88665029 : ℕ)^8233*50000000000000^6185 ≤ 6729853630367^6185*400000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88665029 400000000 6729853630367 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674365869/1250000000 : ℝ)^8233 ≤ (43978421987311/100000000000000 : ℝ)^6185 := by
    have hnat : (674365869 : ℕ)^8233*100000000000000^6185 ≤ 43978421987311^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674365869 1250000000 43978421987311 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105277039/200000000 : ℝ)^8233 ≤ (21280935367543/50000000000000 : ℝ)^6185 := by
    have hnat : (105277039 : ℕ)^8233*50000000000000^6185 ≤ 21280935367543^6185*200000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105277039 200000000 21280935367543 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88665029/400000000 : ℝ), (674365869/1250000000 : ℝ), (105277039/200000000 : ℝ)] ![(6729853630367/50000000000000 : ℝ), (43978421987311/100000000000000 : ℝ), (21280935367543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88665029/400000000 : ℝ)|^8233 ≤ (6729853630367/50000000000000 : ℝ)^6185
        have hw : |(-88665029/400000000 : ℝ)|=(88665029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674365869/1250000000 : ℝ)|^8233 ≤ (43978421987311/100000000000000 : ℝ)^6185
        have hw : |(674365869/1250000000 : ℝ)|=(674365869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105277039/200000000 : ℝ)|^8233 ≤ (21280935367543/50000000000000 : ℝ)^6185
        have hw : |(105277039/200000000 : ℝ)|=(105277039/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672531019/5000000000 : ℝ)*x 0 + (-1141568981/5000000000 : ℝ)*x 1 + (5263851937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672531019/5000000000 : ℝ)^8233 ≤ (43438164141117/100000000000000 : ℝ)^6185 := by
    have hnat : (2672531019 : ℕ)^8233*100000000000000^6185 ≤ 43438164141117^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672531019 5000000000 43438164141117 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141568981/5000000000 : ℝ)^8233 ≤ (6999982625469/50000000000000 : ℝ)^6185 := by
    have hnat : (1141568981 : ℕ)^8233*50000000000000^6185 ≤ 6999982625469^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141568981 5000000000 6999982625469 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263851937/10000000000 : ℝ)^8233 ≤ (42561870595167/100000000000000 : ℝ)^6185 := by
    have hnat : (5263851937 : ℕ)^8233*100000000000000^6185 ≤ 42561870595167^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263851937 10000000000 42561870595167 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672531019/5000000000 : ℝ), (-1141568981/5000000000 : ℝ), (5263851937/10000000000 : ℝ)] ![(43438164141117/100000000000000 : ℝ), (6999982625469/50000000000000 : ℝ), (42561870595167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672531019/5000000000 : ℝ)|^8233 ≤ (43438164141117/100000000000000 : ℝ)^6185
        have hw : |(2672531019/5000000000 : ℝ)|=(2672531019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141568981/5000000000 : ℝ)|^8233 ≤ (6999982625469/50000000000000 : ℝ)^6185
        have hw : |(-1141568981/5000000000 : ℝ)|=(1141568981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263851937/10000000000 : ℝ)|^8233 ≤ (42561870595167/100000000000000 : ℝ)^6185
        have hw : |(5263851937/10000000000 : ℝ)|=(5263851937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345062043/10000000000 : ℝ)*x 0 + (5263851947/10000000000 : ℝ)*x 1 + (-2283137941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345062043/10000000000 : ℝ)^8233 ≤ (21719082097603/50000000000000 : ℝ)^6185 := by
    have hnat : (5345062043 : ℕ)^8233*50000000000000^6185 ≤ 21719082097603^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345062043 10000000000 21719082097603 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263851947/10000000000 : ℝ)^8233 ≤ (42561870702797/100000000000000 : ℝ)^6185 := by
    have hnat : (5263851947 : ℕ)^8233*100000000000000^6185 ≤ 42561870702797^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263851947 10000000000 42561870702797 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283137941/10000000000 : ℝ)^8233 ≤ (1399996507953/10000000000000 : ℝ)^6185 := by
    have hnat : (2283137941 : ℕ)^8233*10000000000000^6185 ≤ 1399996507953^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283137941 10000000000 1399996507953 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345062043/10000000000 : ℝ), (5263851947/10000000000 : ℝ), (-2283137941/10000000000 : ℝ)] ![(21719082097603/50000000000000 : ℝ), (42561870702797/100000000000000 : ℝ), (1399996507953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345062043/10000000000 : ℝ)|^8233 ≤ (21719082097603/50000000000000 : ℝ)^6185
        have hw : |(5345062043/10000000000 : ℝ)|=(5345062043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263851947/10000000000 : ℝ)|^8233 ≤ (42561870702797/100000000000000 : ℝ)^6185
        have hw : |(5263851947/10000000000 : ℝ)|=(5263851947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283137941/10000000000 : ℝ)|^8233 ≤ (1399996507953/10000000000000 : ℝ)^6185
        have hw : |(-2283137941/10000000000 : ℝ)|=(2283137941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379238879/10000000000 : ℝ)*x 0 + (1063339363/2500000000 : ℝ)*x 1 + (1127230263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379238879/10000000000 : ℝ)^8233 ≤ (16658167875417/50000000000000 : ℝ)^6185 := by
    have hnat : (4379238879 : ℕ)^8233*50000000000000^6185 ≤ 16658167875417^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379238879 10000000000 16658167875417 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063339363/2500000000 : ℝ)^8233 ≤ (3204765189337/10000000000000 : ℝ)^6185 := by
    have hnat : (1063339363 : ℕ)^8233*10000000000000^6185 ≤ 3204765189337^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063339363 2500000000 3204765189337 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127230263/2500000000 : ℝ)^8233 ≤ (4329501541687/12500000000000 : ℝ)^6185 := by
    have hnat : (1127230263 : ℕ)^8233*12500000000000^6185 ≤ 4329501541687^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127230263 2500000000 4329501541687 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379238879/10000000000 : ℝ), (1063339363/2500000000 : ℝ), (1127230263/2500000000 : ℝ)] ![(16658167875417/50000000000000 : ℝ), (3204765189337/10000000000000 : ℝ), (4329501541687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379238879/10000000000 : ℝ)|^8233 ≤ (16658167875417/50000000000000 : ℝ)^6185
        have hw : |(4379238879/10000000000 : ℝ)|=(4379238879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063339363/2500000000 : ℝ)|^8233 ≤ (3204765189337/10000000000000 : ℝ)^6185
        have hw : |(1063339363/2500000000 : ℝ)|=(1063339363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127230263/2500000000 : ℝ)|^8233 ≤ (4329501541687/12500000000000 : ℝ)^6185
        have hw : |(1127230263/2500000000 : ℝ)|=(1127230263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108315449/5000000000 : ℝ)*x 0 + (5264180517/10000000000 : ℝ)*x 1 + (539459719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108315449/5000000000 : ℝ)^8233 ≤ (13459749073057/100000000000000 : ℝ)^6185 := by
    have hnat : (1108315449 : ℕ)^8233*100000000000000^6185 ≤ 13459749073057^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108315449 5000000000 13459749073057 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264180517/10000000000 : ℝ)^8233 ≤ (5320675894433/12500000000000 : ℝ)^6185 := by
    have hnat : (5264180517 : ℕ)^8233*12500000000000^6185 ≤ 5320675894433^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264180517 10000000000 5320675894433 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539459719/1000000000 : ℝ)^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185 := by
    have hnat : (539459719 : ℕ)^8233*50000000000000^6185 ≤ 21987421876819^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539459719 1000000000 21987421876819 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108315449/5000000000 : ℝ), (5264180517/10000000000 : ℝ), (539459719/1000000000 : ℝ)] ![(13459749073057/100000000000000 : ℝ), (5320675894433/12500000000000 : ℝ), (21987421876819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108315449/5000000000 : ℝ)|^8233 ≤ (13459749073057/100000000000000 : ℝ)^6185
        have hw : |(-1108315449/5000000000 : ℝ)|=(1108315449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264180517/10000000000 : ℝ)|^8233 ≤ (5320675894433/12500000000000 : ℝ)^6185
        have hw : |(5264180517/10000000000 : ℝ)|=(5264180517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539459719/1000000000 : ℝ)|^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185
        have hw : |(539459719/1000000000 : ℝ)|=(539459719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062423167/2000000000 : ℝ)*x 0 + (-134524543/625000000 : ℝ)*x 1 + (539459719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062423167/2000000000 : ℝ)^8233 ≤ (21541062207479/50000000000000 : ℝ)^6185 := by
    have hnat : (1062423167 : ℕ)^8233*50000000000000^6185 ≤ 21541062207479^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062423167 2000000000 21541062207479 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134524543/625000000 : ℝ)^8233 ≤ (6471515906983/50000000000000 : ℝ)^6185 := by
    have hnat : (134524543 : ℕ)^8233*50000000000000^6185 ≤ 6471515906983^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134524543 625000000 6471515906983 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539459719/1000000000 : ℝ)^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185 := by
    have hnat : (539459719 : ℕ)^8233*50000000000000^6185 ≤ 21987421876819^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539459719 1000000000 21987421876819 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062423167/2000000000 : ℝ), (-134524543/625000000 : ℝ), (539459719/1000000000 : ℝ)] ![(21541062207479/50000000000000 : ℝ), (6471515906983/50000000000000 : ℝ), (21987421876819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062423167/2000000000 : ℝ)|^8233 ≤ (21541062207479/50000000000000 : ℝ)^6185
        have hw : |(1062423167/2000000000 : ℝ)|=(1062423167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134524543/625000000 : ℝ)|^8233 ≤ (6471515906983/50000000000000 : ℝ)^6185
        have hw : |(-134524543/625000000 : ℝ)|=(134524543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539459719/1000000000 : ℝ)|^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185
        have hw : |(539459719/1000000000 : ℝ)|=(539459719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062423167/2000000000 : ℝ)*x 0 + (539459719/1000000000 : ℝ)*x 1 + (-134524543/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062423167/2000000000 : ℝ)^8233 ≤ (21541062207479/50000000000000 : ℝ)^6185 := by
    have hnat : (1062423167 : ℕ)^8233*50000000000000^6185 ≤ 21541062207479^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062423167 2000000000 21541062207479 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539459719/1000000000 : ℝ)^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185 := by
    have hnat : (539459719 : ℕ)^8233*50000000000000^6185 ≤ 21987421876819^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539459719 1000000000 21987421876819 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134524543/625000000 : ℝ)^8233 ≤ (6471515906983/50000000000000 : ℝ)^6185 := by
    have hnat : (134524543 : ℕ)^8233*50000000000000^6185 ≤ 6471515906983^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134524543 625000000 6471515906983 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062423167/2000000000 : ℝ), (539459719/1000000000 : ℝ), (-134524543/625000000 : ℝ)] ![(21541062207479/50000000000000 : ℝ), (21987421876819/50000000000000 : ℝ), (6471515906983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062423167/2000000000 : ℝ)|^8233 ≤ (21541062207479/50000000000000 : ℝ)^6185
        have hw : |(1062423167/2000000000 : ℝ)|=(1062423167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539459719/1000000000 : ℝ)|^8233 ≤ (21987421876819/50000000000000 : ℝ)^6185
        have hw : |(539459719/1000000000 : ℝ)|=(539459719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134524543/625000000 : ℝ)|^8233 ≤ (6471515906983/50000000000000 : ℝ)^6185
        have hw : |(-134524543/625000000 : ℝ)|=(134524543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s7_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875849783/2000000000 : ℝ)*x 0 + (2254140193/5000000000 : ℝ)*x 1 + (1063500113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875849783/2000000000 : ℝ)^8233 ≤ (6663287476911/20000000000000 : ℝ)^6185 := by
    have hnat : (875849783 : ℕ)^8233*20000000000000^6185 ≤ 6663287476911^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875849783 2000000000 6663287476911 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254140193/5000000000 : ℝ)^8233 ≤ (34629461521651/100000000000000 : ℝ)^6185 := by
    have hnat : (2254140193 : ℕ)^8233*100000000000000^6185 ≤ 34629461521651^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254140193 5000000000 34629461521651 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063500113/2500000000 : ℝ)^8233 ≤ (32054101074669/100000000000000 : ℝ)^6185 := by
    have hnat : (1063500113 : ℕ)^8233*100000000000000^6185 ≤ 32054101074669^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063500113 2500000000 32054101074669 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875849783/2000000000 : ℝ), (2254140193/5000000000 : ℝ), (1063500113/2500000000 : ℝ)] ![(6663287476911/20000000000000 : ℝ), (34629461521651/100000000000000 : ℝ), (32054101074669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875849783/2000000000 : ℝ)|^8233 ≤ (6663287476911/20000000000000 : ℝ)^6185
        have hw : |(875849783/2000000000 : ℝ)|=(875849783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254140193/5000000000 : ℝ)|^8233 ≤ (34629461521651/100000000000000 : ℝ)^6185
        have hw : |(2254140193/5000000000 : ℝ)|=(2254140193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063500113/2500000000 : ℝ)|^8233 ≤ (32054101074669/100000000000000 : ℝ)^6185
        have hw : |(1063500113/2500000000 : ℝ)|=(1063500113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11213/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5601/50000 : ℝ) ^ (1029/256 : ℝ) ≤ (15087379948395007/100000000000000000000 : ℝ) := by
    have hpowers : (5601/50000 : ℝ)^1029 ≤ (15087379948395007/100000000000000000000 : ℝ)^256 := by
      have hnat : (5601 : ℕ)^1029*100000000000000000000^256 ≤ 15087379948395007^256*50000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5601 50000 15087379948395007 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5601/50000 : ℝ)) (X := (15087379948395007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7/50 : ℝ) ^ (1029/256 : ℝ) ≤ (1478750645584247/4000000000000000000 : ℝ) := by
    have hpowers : (7/50 : ℝ)^1029 ≤ (1478750645584247/4000000000000000000 : ℝ)^256 := by
      have hnat : (7 : ℕ)^1029*4000000000000000000^256 ≤ 1478750645584247^256*50^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 50 1478750645584247 4000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/50 : ℝ)) (X := (1478750645584247/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015087379948395007/50000000000000000000 : ℝ) ≤ (20001501236769/20000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50015087379948395007/50000000000000000000 : ℝ)^256 ≤ (20001501236769/20000000000000 : ℝ)^1029 := by
      have hnat : (50015087379948395007 : ℕ)^256*20000000000000^1029 ≤ 20001501236769^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015087379948395007 50000000000000000000 20001501236769 20000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20001501236769/20000000000000 : ℝ)) (X := (50015087379948395007/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026028073044000591/50000000000000000000 : ℝ) ≤ (10001294826873453/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50026028073044000591/50000000000000000000 : ℝ)^256 ≤ (10001294826873453/10000000000000000 : ℝ)^1029 := by
      have hnat : (50026028073044000591 : ℕ)^256*10000000000000000^1029 ≤ 10001294826873453^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026028073044000591 50000000000000000000 10001294826873453 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001294826873453/10000000000000000 : ℝ)) (X := (50026028073044000591/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001478750645584247/2000000000000000000 : ℝ) ≤ (5000919517681203/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (2001478750645584247/2000000000000000000 : ℝ)^256 ≤ (5000919517681203/5000000000000000 : ℝ)^1029 := by
      have hnat : (2001478750645584247 : ℕ)^256*5000000000000000^1029 ≤ 5000919517681203^1029*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001478750645584247 2000000000000000000 5000919517681203 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000919517681203/5000000000000000 : ℝ)) (X := (2001478750645584247/2000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15087379948395007/100000000000000000000 : ℝ) ≤ ((6992476945813331997/6995000000000000000 : ℝ)+2*(544208488953/279800000000000 : ℝ)*(5601/50000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (6992476945813331997/6995000000000000000 : ℝ)+2*(544208488953/279800000000000 : ℝ)*(5601/50000 : ℝ)=(20001501236769/20000000000000 : ℝ) by norm_num, show 1+2*(15087379948395007/100000000000000000000 : ℝ)=(50015087379948395007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1478750645584247/4000000000000000000 : ℝ)+(15087379948395007/100000000000000000000 : ℝ) ≤ ((6992476945813331997/6995000000000000000 : ℝ)+(544208488953/279800000000000 : ℝ)*((7/50 : ℝ)+(5601/50000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (6992476945813331997/6995000000000000000 : ℝ)+(544208488953/279800000000000 : ℝ)*((7/50 : ℝ)+(5601/50000 : ℝ))=(10001294826873453/10000000000000000 : ℝ) by norm_num, show 1+(1478750645584247/4000000000000000000 : ℝ)+(15087379948395007/100000000000000000000 : ℝ)=(50026028073044000591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1478750645584247/4000000000000000000 : ℝ) ≤ ((6992476945813331997/6995000000000000000 : ℝ)+2*(544208488953/279800000000000 : ℝ)*(7/50 : ℝ))^(1029/256 : ℝ) := by
    rw [show (6992476945813331997/6995000000000000000 : ℝ)+2*(544208488953/279800000000000 : ℝ)*(7/50 : ℝ)=(5000919517681203/5000000000000000 : ℝ) by norm_num, show 1+2*(1478750645584247/4000000000000000000 : ℝ)=(2001478750645584247/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6992476945813331997/6995000000000000000 : ℝ)*(X 1 0+X 2 0)+(544208488953/279800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (6992476945813331997/6995000000000000000 : ℝ)) (alpha := (544208488953/279800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6992476945813331997/6995000000000000000 : ℝ)*(X 0 1+X 2 1)+(544208488953/279800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (6992476945813331997/6995000000000000000 : ℝ)) (alpha := (544208488953/279800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6992476945813331997/6995000000000000000 : ℝ)*(X 0 2+X 1 2)+(544208488953/279800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7/50 : ℝ)) (c := (6992476945813331997/6995000000000000000 : ℝ)) (alpha := (544208488953/279800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88665029/400000000 : ℝ)*X 0 0+(674365869/1250000000 : ℝ)*X 0 1+(105277039/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672531019/5000000000 : ℝ)*X 1 0+(-1141568981/5000000000 : ℝ)*X 1 1+(5263851937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345062043/10000000000 : ℝ)*X 2 0+(5263851947/10000000000 : ℝ)*X 2 1+(-2283137941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379238879/10000000000 : ℝ)*X 0 0+(1063339363/2500000000 : ℝ)*X 0 1+(1127230263/2500000000 : ℝ)*X 0 2+(4379238879/10000000000 : ℝ)*X 1 0+(1063339363/2500000000 : ℝ)*X 1 1+(1127230263/2500000000 : ℝ)*X 1 2+(4379238879/10000000000 : ℝ)*X 2 0+(1063339363/2500000000 : ℝ)*X 2 1+(1127230263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1108315449/5000000000 : ℝ)*X 0 0+(5264180517/10000000000 : ℝ)*X 0 1+(539459719/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062423167/2000000000 : ℝ)*X 1 0+(-134524543/625000000 : ℝ)*X 1 1+(539459719/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062423167/2000000000 : ℝ)*X 2 0+(539459719/1000000000 : ℝ)*X 2 1+(-134524543/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875849783/2000000000 : ℝ)*X 0 0+(2254140193/5000000000 : ℝ)*X 0 1+(1063500113/2500000000 : ℝ)*X 0 2+(875849783/2000000000 : ℝ)*X 1 0+(2254140193/5000000000 : ℝ)*X 1 1+(1063500113/2500000000 : ℝ)*X 1 2+(875849783/2000000000 : ℝ)*X 2 0+(2254140193/5000000000 : ℝ)*X 2 1+(1063500113/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (591830329452921744500962911/174875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648810513/100000000000000 : ℝ)*(base19) + (57132179/10000000000000 : ℝ)*(base23) + (11308207/25000000000000 : ℝ)*(lower2) + (41649303/50000000000000 : ℝ)*(upper3) + (213781/400000000000 : ℝ)*(upper5) + (5771095568484379/100000000000000 : ℝ)*(major0) + (5771095568484379/100000000000000 : ℝ)*(major1) + (5771095568484379/100000000000000 : ℝ)*(major2) + (1907309036593989/25000000000000 : ℝ)*(sp0) + (1907312967649963/25000000000000 : ℝ)*(sp1) + (3814625974044287/50000000000000 : ℝ)*(sp2) + (1956464414926777/50000000000000 : ℝ)*(sp3) + (16373034409/100000000000000 : ℝ)*(sp4) + (1209361833/12500000000000 : ℝ)*(sp7) + (1956469252374109/50000000000000 : ℝ)*(f.failure) + (1525850503882073/20000000000000 : ℝ)*(f.sum) + (3839248330627/13990000000000000000000000000 : ℝ)*base65 + (6176823085603549863/699500000000000000000000000000000 : ℝ)*base67 + (3798934693088049863/699500000000000000000000000000000 : ℝ)*base69 + (2803125054916049863/699500000000000000000000000000000 : ℝ)*base71 + (72718018035933/13990000000000000000000000000 : ℝ)*base74 + (4978509647495049863/699500000000000000000000000000000 : ℝ)*base75 + (1446881870130950137/699500000000000000000000000000000 : ℝ)*base78 + (19466778865510049863/699500000000000000000000000000000 : ℝ)*base79 + (22428563545207/13990000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2512141/500000000000000000000 : ℝ)*base90 + (2512141/500000000000000000000 : ℝ)*base92 + (2512141/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83897367422820807744489/13990000000000000000000000000 : ℝ) := by norm_num
    linear_combination (561757579/50000000000000 : ℝ)*(base19) + (1222326819/100000000000000 : ℝ)*(base23) + (60164633/50000000000000 : ℝ)*(upper3) + (8990363/20000000000000 : ℝ)*(lower4) + (12255097/10000000000000 : ℝ)*(upper5) + (5800201834691357/100000000000000 : ℝ)*(major0) + (5800201834691357/100000000000000 : ℝ)*(major1) + (5800201834691357/100000000000000 : ℝ)*(major2) + (30371635997/100000000000000 : ℝ)*(sp1) + (32659628261/100000000000000 : ℝ)*(sp2) + (383386511590189/5000000000000 : ℝ)*(sp4) + (61341589893221/800000000000 : ℝ)*(sp5) + (7667696349848701/100000000000000 : ℝ)*(sp6) + (491584154710063/12500000000000 : ℝ)*(sp7) + (491584154710063/12500000000000 : ℝ)*(f.failure) + (383386511590189/5000000000000 : ℝ)*(f.sum) + (35903948413579/13990000000000000000000000000 : ℝ)*base66 + (3250335638849974929/699500000000000000000000000000000 : ℝ)*base67 + (2922118204651974929/699500000000000000000000000000000 : ℝ)*base69 + (14638469691491525071/699500000000000000000000000000000 : ℝ)*base72 + (16848333236479/13990000000000000000000000000 : ℝ)*base74 + (21613372548221474929/699500000000000000000000000000000 : ℝ)*base75 + (5630084009993025071/699500000000000000000000000000000 : ℝ)*base78 + (1546744494001525071/699500000000000000000000000000000 : ℝ)*base80 + (16688406397589/13990000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (131313/125000000000000000000 : ℝ)*base89 + (131313/125000000000000000000 : ℝ)*base91 + (131313/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s8_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216634503/10000000000 : ℝ)*x 0 + (5394807687/10000000000 : ℝ)*x 1 + (5263965597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216634503/10000000000 : ℝ)^8233 ≤ (1345977821157/10000000000000 : ℝ)^6185 := by
    have hnat : (2216634503 : ℕ)^8233*10000000000000^6185 ≤ 1345977821157^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216634503 10000000000 1345977821157 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394807687/10000000000 : ℝ)^8233 ≤ (43977127839423/100000000000000 : ℝ)^6185 := by
    have hnat : (5394807687 : ℕ)^8233*100000000000000^6185 ≤ 43977127839423^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394807687 10000000000 43977127839423 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263965597/10000000000 : ℝ)^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185 := by
    have hnat : (5263965597 : ℕ)^8233*100000000000000^6185 ≤ 42563093928073^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263965597 10000000000 42563093928073 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216634503/10000000000 : ℝ), (5394807687/10000000000 : ℝ), (5263965597/10000000000 : ℝ)] ![(1345977821157/10000000000000 : ℝ), (43977127839423/100000000000000 : ℝ), (42563093928073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216634503/10000000000 : ℝ)|^8233 ≤ (1345977821157/10000000000000 : ℝ)^6185
        have hw : |(-2216634503/10000000000 : ℝ)|=(2216634503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394807687/10000000000 : ℝ)|^8233 ≤ (43977127839423/100000000000000 : ℝ)^6185
        have hw : |(5394807687/10000000000 : ℝ)|=(5394807687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263965597/10000000000 : ℝ)|^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185
        have hw : |(5263965597/10000000000 : ℝ)|=(5263965597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672516419/5000000000 : ℝ)*x 0 + (-456605357/2000000000 : ℝ)*x 1 + (5263965597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672516419/5000000000 : ℝ)^8233 ≤ (4343784826297/10000000000000 : ℝ)^6185 := by
    have hnat : (2672516419 : ℕ)^8233*10000000000000^6185 ≤ 4343784826297^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672516419 5000000000 4343784826297 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456605357/2000000000 : ℝ)^8233 ≤ (6999528898423/50000000000000 : ℝ)^6185 := by
    have hnat : (456605357 : ℕ)^8233*50000000000000^6185 ≤ 6999528898423^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456605357 2000000000 6999528898423 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263965597/10000000000 : ℝ)^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185 := by
    have hnat : (5263965597 : ℕ)^8233*100000000000000^6185 ≤ 42563093928073^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263965597 10000000000 42563093928073 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672516419/5000000000 : ℝ), (-456605357/2000000000 : ℝ), (5263965597/10000000000 : ℝ)] ![(4343784826297/10000000000000 : ℝ), (6999528898423/50000000000000 : ℝ), (42563093928073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672516419/5000000000 : ℝ)|^8233 ≤ (4343784826297/10000000000000 : ℝ)^6185
        have hw : |(2672516419/5000000000 : ℝ)|=(2672516419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456605357/2000000000 : ℝ)|^8233 ≤ (6999528898423/50000000000000 : ℝ)^6185
        have hw : |(-456605357/2000000000 : ℝ)|=(456605357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263965597/10000000000 : ℝ)|^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185
        have hw : |(5263965597/10000000000 : ℝ)|=(5263965597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345032839/10000000000 : ℝ)*x 0 + (5263965597/10000000000 : ℝ)*x 1 + (-2283026783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345032839/10000000000 : ℝ)^8233 ≤ (10859462068447/25000000000000 : ℝ)^6185 := by
    have hnat : (5345032839 : ℕ)^8233*25000000000000^6185 ≤ 10859462068447^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345032839 10000000000 10859462068447 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263965597/10000000000 : ℝ)^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185 := by
    have hnat : (5263965597 : ℕ)^8233*100000000000000^6185 ≤ 42563093928073^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263965597 10000000000 42563093928073 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283026783/10000000000 : ℝ)^8233 ≤ (6999528890261/50000000000000 : ℝ)^6185 := by
    have hnat : (2283026783 : ℕ)^8233*50000000000000^6185 ≤ 6999528890261^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283026783 10000000000 6999528890261 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345032839/10000000000 : ℝ), (5263965597/10000000000 : ℝ), (-2283026783/10000000000 : ℝ)] ![(10859462068447/25000000000000 : ℝ), (42563093928073/100000000000000 : ℝ), (6999528890261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345032839/10000000000 : ℝ)|^8233 ≤ (10859462068447/25000000000000 : ℝ)^6185
        have hw : |(5345032839/10000000000 : ℝ)|=(5345032839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263965597/10000000000 : ℝ)|^8233 ≤ (42563093928073/100000000000000 : ℝ)^6185
        have hw : |(5263965597/10000000000 : ℝ)|=(5263965597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283026783/10000000000 : ℝ)|^8233 ≤ (6999528890261/50000000000000 : ℝ)^6185
        have hw : |(-2283026783/10000000000 : ℝ)|=(2283026783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094811203/2500000000 : ℝ)*x 0 + (2126791891/5000000000 : ℝ)*x 1 + (2254346587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094811203/2500000000 : ℝ)^8233 ≤ (33316395833813/100000000000000 : ℝ)^6185 := by
    have hnat : (1094811203 : ℕ)^8233*100000000000000^6185 ≤ 33316395833813^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094811203 2500000000 33316395833813 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126791891/5000000000 : ℝ)^8233 ≤ (32049921908193/100000000000000 : ℝ)^6185 := by
    have hnat : (2126791891 : ℕ)^8233*100000000000000^6185 ≤ 32049921908193^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126791891 5000000000 32049921908193 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254346587/5000000000 : ℝ)^8233 ≤ (34633682244917/100000000000000 : ℝ)^6185 := by
    have hnat : (2254346587 : ℕ)^8233*100000000000000^6185 ≤ 34633682244917^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254346587 5000000000 34633682244917 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094811203/2500000000 : ℝ), (2126791891/5000000000 : ℝ), (2254346587/5000000000 : ℝ)] ![(33316395833813/100000000000000 : ℝ), (32049921908193/100000000000000 : ℝ), (34633682244917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094811203/2500000000 : ℝ)|^8233 ≤ (33316395833813/100000000000000 : ℝ)^6185
        have hw : |(1094811203/2500000000 : ℝ)|=(1094811203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126791891/5000000000 : ℝ)|^8233 ≤ (32049921908193/100000000000000 : ℝ)^6185
        have hw : |(2126791891/5000000000 : ℝ)|=(2126791891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254346587/5000000000 : ℝ)|^8233 ≤ (34633682244917/100000000000000 : ℝ)^6185
        have hw : |(2254346587/5000000000 : ℝ)|=(2254346587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216639613/10000000000 : ℝ)*x 0 + (2632146481/5000000000 : ℝ)*x 1 + (134861979/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216639613/10000000000 : ℝ)^8233 ≤ (13459819514731/100000000000000 : ℝ)^6185 := by
    have hnat : (2216639613 : ℕ)^8233*100000000000000^6185 ≤ 13459819514731^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216639613 10000000000 13459819514731 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632146481/5000000000 : ℝ)^8233 ≤ (42566617436183/100000000000000 : ℝ)^6185 := by
    have hnat : (2632146481 : ℕ)^8233*100000000000000^6185 ≤ 42566617436183^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632146481 5000000000 42566617436183 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134861979/250000000 : ℝ)^8233 ≤ (8794712606529/20000000000000 : ℝ)^6185 := by
    have hnat : (134861979 : ℕ)^8233*20000000000000^6185 ≤ 8794712606529^6185*250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134861979 250000000 8794712606529 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216639613/10000000000 : ℝ), (2632146481/5000000000 : ℝ), (134861979/250000000 : ℝ)] ![(13459819514731/100000000000000 : ℝ), (42566617436183/100000000000000 : ℝ), (8794712606529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216639613/10000000000 : ℝ)|^8233 ≤ (13459819514731/100000000000000 : ℝ)^6185
        have hw : |(-2216639613/10000000000 : ℝ)|=(2216639613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632146481/5000000000 : ℝ)|^8233 ≤ (42566617436183/100000000000000 : ℝ)^6185
        have hw : |(2632146481/5000000000 : ℝ)|=(2632146481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134861979/250000000 : ℝ)|^8233 ≤ (8794712606529/20000000000000 : ℝ)^6185
        have hw : |(134861979/250000000 : ℝ)|=(134861979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664018153/1250000000 : ℝ)*x 0 + (-269064137/1250000000 : ℝ)*x 1 + (2697239563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664018153/1250000000 : ℝ)^8233 ≤ (21541220844007/50000000000000 : ℝ)^6185 := by
    have hnat : (664018153 : ℕ)^8233*50000000000000^6185 ≤ 21541220844007^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664018153 1250000000 21541220844007 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269064137/1250000000 : ℝ)^8233 ≤ (12943995625873/100000000000000 : ℝ)^6185 := by
    have hnat : (269064137 : ℕ)^8233*100000000000000^6185 ≤ 12943995625873^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269064137 1250000000 12943995625873 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697239563/5000000000 : ℝ)^8233 ≤ (21986781331859/50000000000000 : ℝ)^6185 := by
    have hnat : (2697239563 : ℕ)^8233*50000000000000^6185 ≤ 21986781331859^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697239563 5000000000 21986781331859 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664018153/1250000000 : ℝ), (-269064137/1250000000 : ℝ), (2697239563/5000000000 : ℝ)] ![(21541220844007/50000000000000 : ℝ), (12943995625873/100000000000000 : ℝ), (21986781331859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664018153/1250000000 : ℝ)|^8233 ≤ (21541220844007/50000000000000 : ℝ)^6185
        have hw : |(664018153/1250000000 : ℝ)|=(664018153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269064137/1250000000 : ℝ)|^8233 ≤ (12943995625873/100000000000000 : ℝ)^6185
        have hw : |(-269064137/1250000000 : ℝ)|=(269064137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697239563/5000000000 : ℝ)|^8233 ≤ (21986781331859/50000000000000 : ℝ)^6185
        have hw : |(2697239563/5000000000 : ℝ)|=(2697239563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062428983/2000000000 : ℝ)*x 0 + (5394479067/10000000000 : ℝ)*x 1 + (-1076256797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062428983/2000000000 : ℝ)^8233 ≤ (43082438352159/100000000000000 : ℝ)^6185 := by
    have hnat : (1062428983 : ℕ)^8233*100000000000000^6185 ≤ 43082438352159^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062428983 2000000000 43082438352159 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394479067/10000000000 : ℝ)^8233 ≤ (43973562023523/100000000000000 : ℝ)^6185 := by
    have hnat : (5394479067 : ℕ)^8233*100000000000000^6185 ≤ 43973562023523^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394479067 10000000000 43973562023523 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076256797/5000000000 : ℝ)^8233 ≤ (808999975761/6250000000000 : ℝ)^6185 := by
    have hnat : (1076256797 : ℕ)^8233*6250000000000^6185 ≤ 808999975761^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076256797 5000000000 808999975761 6250000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062428983/2000000000 : ℝ), (5394479067/10000000000 : ℝ), (-1076256797/5000000000 : ℝ)] ![(43082438352159/100000000000000 : ℝ), (43973562023523/100000000000000 : ℝ), (808999975761/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062428983/2000000000 : ℝ)|^8233 ≤ (43082438352159/100000000000000 : ℝ)^6185
        have hw : |(1062428983/2000000000 : ℝ)|=(1062428983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394479067/10000000000 : ℝ)|^8233 ≤ (43973562023523/100000000000000 : ℝ)^6185
        have hw : |(5394479067/10000000000 : ℝ)|=(5394479067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076256797/5000000000 : ℝ)|^8233 ≤ (808999975761/6250000000000 : ℝ)^6185
        have hw : |(-1076256797/5000000000 : ℝ)|=(1076256797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s8_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189627193/5000000000 : ℝ)*x 0 + (45080549/100000000 : ℝ)*x 1 + (4254224787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189627193/5000000000 : ℝ)^8233 ≤ (1665824639447/5000000000000 : ℝ)^6185 := by
    have hnat : (2189627193 : ℕ)^8233*5000000000000^6185 ≤ 1665824639447^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189627193 5000000000 1665824639447 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45080549/100000000 : ℝ)^8233 ≤ (17313577999967/50000000000000 : ℝ)^6185 := by
    have hnat : (45080549 : ℕ)^8233*50000000000000^6185 ≤ 17313577999967^6185*100000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45080549 100000000 17313577999967 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254224787/10000000000 : ℝ)^8233 ≤ (32056351192751/100000000000000 : ℝ)^6185 := by
    have hnat : (4254224787 : ℕ)^8233*100000000000000^6185 ≤ 32056351192751^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254224787 10000000000 32056351192751 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189627193/5000000000 : ℝ), (45080549/100000000 : ℝ), (4254224787/10000000000 : ℝ)] ![(1665824639447/5000000000000 : ℝ), (17313577999967/50000000000000 : ℝ), (32056351192751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189627193/5000000000 : ℝ)|^8233 ≤ (1665824639447/5000000000000 : ℝ)^6185
        have hw : |(2189627193/5000000000 : ℝ)|=(2189627193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45080549/100000000 : ℝ)|^8233 ≤ (17313577999967/50000000000000 : ℝ)^6185
        have hw : |(45080549/100000000 : ℝ)|=(45080549/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254224787/10000000000 : ℝ)|^8233 ≤ (32056351192751/100000000000000 : ℝ)^6185
        have hw : |(4254224787/10000000000 : ℝ)|=(4254224787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11213/100000 : ℝ) ^ (1029/256 : ℝ) ≤ (15147018922092019/100000000000000000000 : ℝ) := by
    have hpowers : (11213/100000 : ℝ)^1029 ≤ (15147018922092019/100000000000000000000 : ℝ)^256 := by
      have hnat : (11213 : ℕ)^1029*100000000000000000000^256 ≤ 15147018922092019^256*100000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11213 100000 15147018922092019 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11213/100000 : ℝ)) (X := (15147018922092019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13989/100000 : ℝ) ^ (1029/256 : ℝ) ≤ (18426074846715809/50000000000000000000 : ℝ) := by
    have hpowers : (13989/100000 : ℝ)^1029 ≤ (18426074846715809/50000000000000000000 : ℝ)^256 := by
      have hnat : (13989 : ℕ)^1029*50000000000000000000^256 ≤ 18426074846715809^256*100000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13989 100000 18426074846715809 50000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13989/100000 : ℝ)) (X := (18426074846715809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015147018922092019/50000000000000000000 : ℝ) ≤ (1250094198146229/1250000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50015147018922092019/50000000000000000000 : ℝ)^256 ≤ (1250094198146229/1250000000000000 : ℝ)^1029 := by
      have hnat : (50015147018922092019 : ℕ)^256*1250000000000000^1029 ≤ 1250094198146229^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015147018922092019 50000000000000000000 1250094198146229 1250000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094198146229/1250000000000000 : ℝ)) (X := (50015147018922092019/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051999168615523637/100000000000000000000 : ℝ) ≤ (10001293409911871/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100051999168615523637/100000000000000000000 : ℝ)^256 ≤ (10001293409911871/10000000000000000 : ℝ)^1029 := by
      have hnat : (100051999168615523637 : ℕ)^256*10000000000000000^1029 ≤ 10001293409911871^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051999168615523637 100000000000000000000 10001293409911871 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293409911871/10000000000000000 : ℝ)) (X := (100051999168615523637/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018426074846715809/25000000000000000000 : ℝ) ≤ (1000183323465391/1000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (25018426074846715809/25000000000000000000 : ℝ)^256 ≤ (1000183323465391/1000000000000000 : ℝ)^1029 := by
      have hnat : (25018426074846715809 : ℕ)^256*1000000000000000^1029 ≤ 1000183323465391^1029*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018426074846715809 25000000000000000000 1000183323465391 1000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000183323465391/1000000000000000 : ℝ)) (X := (25018426074846715809/25000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15147018922092019/100000000000000000000 : ℝ) ≤ ((13874992921383243509/13880000000000000000 : ℝ)+2*(539824742039/277600000000000 : ℝ)*(11213/100000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (13874992921383243509/13880000000000000000 : ℝ)+2*(539824742039/277600000000000 : ℝ)*(11213/100000 : ℝ)=(1250094198146229/1250000000000000 : ℝ) by norm_num, show 1+2*(15147018922092019/100000000000000000000 : ℝ)=(50015147018922092019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18426074846715809/50000000000000000000 : ℝ)+(15147018922092019/100000000000000000000 : ℝ) ≤ ((13874992921383243509/13880000000000000000 : ℝ)+(539824742039/277600000000000 : ℝ)*((13989/100000 : ℝ)+(11213/100000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (13874992921383243509/13880000000000000000 : ℝ)+(539824742039/277600000000000 : ℝ)*((13989/100000 : ℝ)+(11213/100000 : ℝ))=(10001293409911871/10000000000000000 : ℝ) by norm_num, show 1+(18426074846715809/50000000000000000000 : ℝ)+(15147018922092019/100000000000000000000 : ℝ)=(100051999168615523637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18426074846715809/50000000000000000000 : ℝ) ≤ ((13874992921383243509/13880000000000000000 : ℝ)+2*(539824742039/277600000000000 : ℝ)*(13989/100000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (13874992921383243509/13880000000000000000 : ℝ)+2*(539824742039/277600000000000 : ℝ)*(13989/100000 : ℝ)=(1000183323465391/1000000000000000 : ℝ) by norm_num, show 1+2*(18426074846715809/50000000000000000000 : ℝ)=(25018426074846715809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13874992921383243509/13880000000000000000 : ℝ)*(X 1 0+X 2 0)+(539824742039/277600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13874992921383243509/13880000000000000000 : ℝ)) (alpha := (539824742039/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13874992921383243509/13880000000000000000 : ℝ)*(X 0 1+X 2 1)+(539824742039/277600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13874992921383243509/13880000000000000000 : ℝ)) (alpha := (539824742039/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13874992921383243509/13880000000000000000 : ℝ)*(X 0 2+X 1 2)+(539824742039/277600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13874992921383243509/13880000000000000000 : ℝ)) (alpha := (539824742039/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2216634503/10000000000 : ℝ)*X 0 0+(5394807687/10000000000 : ℝ)*X 0 1+(5263965597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672516419/5000000000 : ℝ)*X 1 0+(-456605357/2000000000 : ℝ)*X 1 1+(5263965597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345032839/10000000000 : ℝ)*X 2 0+(5263965597/10000000000 : ℝ)*X 2 1+(-2283026783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094811203/2500000000 : ℝ)*X 0 0+(2126791891/5000000000 : ℝ)*X 0 1+(2254346587/5000000000 : ℝ)*X 0 2+(1094811203/2500000000 : ℝ)*X 1 0+(2126791891/5000000000 : ℝ)*X 1 1+(2254346587/5000000000 : ℝ)*X 1 2+(1094811203/2500000000 : ℝ)*X 2 0+(2126791891/5000000000 : ℝ)*X 2 1+(2254346587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216639613/10000000000 : ℝ)*X 0 0+(2632146481/5000000000 : ℝ)*X 0 1+(134861979/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664018153/1250000000 : ℝ)*X 1 0+(-269064137/1250000000 : ℝ)*X 1 1+(2697239563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062428983/2000000000 : ℝ)*X 2 0+(5394479067/10000000000 : ℝ)*X 2 1+(-1076256797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189627193/5000000000 : ℝ)*X 0 0+(45080549/100000000 : ℝ)*X 0 1+(4254224787/10000000000 : ℝ)*X 0 2+(2189627193/5000000000 : ℝ)*X 1 0+(45080549/100000000 : ℝ)*X 1 1+(4254224787/10000000000 : ℝ)*X 1 2+(2189627193/5000000000 : ℝ)*X 2 0+(45080549/100000000 : ℝ)*X 2 1+(4254224787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2469927067363003115821784643/347000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28751227/2000000000000 : ℝ)*(base19) + (1338992337/100000000000000 : ℝ)*(base23) + (53449749/100000000000000 : ℝ)*(lower2) + (89846883/50000000000000 : ℝ)*(upper3) + (54000133/50000000000000 : ℝ)*(upper5) + (2890701691716291/50000000000000 : ℝ)*(major0) + (2890701691716291/50000000000000 : ℝ)*(major1) + (2890701691716291/50000000000000 : ℝ)*(major2) + (7642840686365591/100000000000000 : ℝ)*(sp0) + (1910719411591003/25000000000000 : ℝ)*(sp1) + (305715109797321/4000000000000 : ℝ)*(sp2) + (244994137282389/6250000000000 : ℝ)*(sp3) + (9599389943/25000000000000 : ℝ)*(sp4) + (21249156723/100000000000000 : ℝ)*(sp7) + (3919927445674947/100000000000000 : ℝ)*(f.failure) + (3821439541962681/50000000000000 : ℝ)*(f.sum) + (5733752954231/6940000000000000000000000000 : ℝ)*base66 + (3364739391543244881/694000000000000000000000000000000 : ℝ)*base68 + (4374775136606755119/694000000000000000000000000000000 : ℝ)*base69 + (8110718228194755119/694000000000000000000000000000000 : ℝ)*base71 + (20476519811771/6940000000000000000000000000 : ℝ)*base74 + (1461744610391244881/694000000000000000000000000000000 : ℝ)*base76 + (8777525976408755119/694000000000000000000000000000000 : ℝ)*base77 + (8755194547120755119/694000000000000000000000000000000 : ℝ)*base79 + (42182153712531/6940000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (241197/1000000000000000000000 : ℝ)*base89 + (241197/1000000000000000000000 : ℝ)*base91 + (241197/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1043225646318215981816342427/86750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404859353/20000000000000 : ℝ)*(base19) + (36817159/2500000000000 : ℝ)*(base23) + (365293293/100000000000000 : ℝ)*(lower1) + (31811893/50000000000000 : ℝ)*(upper2) + (67462429/100000000000000 : ℝ)*(upper3) + (227113071/100000000000000 : ℝ)*(upper5) + (1452612270565299/25000000000000 : ℝ)*(major0) + (1452612270565299/25000000000000 : ℝ)*(major1) + (1452612270565299/25000000000000 : ℝ)*(major2) + (2267111903/6250000000000 : ℝ)*(sp1) + (7681276651166743/100000000000000 : ℝ)*(sp4) + (768123835307953/10000000000000 : ℝ)*(sp5) + (30004981165939/390625000000 : ℝ)*(sp6) + (1969810556250219/50000000000000 : ℝ)*(sp7) + (1969810556250219/50000000000000 : ℝ)*(f.failure) + (7681276651166743/100000000000000 : ℝ)*(f.sum) + (447965691431/3470000000000000000000000000 : ℝ)*base65 + (2146670865633444191/347000000000000000000000000000000 : ℝ)*base67 + (1249322230506555809/347000000000000000000000000000000 : ℝ)*base70 + (3057959404271444191/347000000000000000000000000000000 : ℝ)*base71 + (11114950313861/3470000000000000000000000000 : ℝ)*base73 + (6154432041961444191/347000000000000000000000000000000 : ℝ)*base75 + (4785862832319444191/347000000000000000000000000000000 : ℝ)*base77 + (3501789505819444191/347000000000000000000000000000000 : ℝ)*base79 + (64542309732039/3470000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6273531/500000000000000000000 : ℝ)*base90 + (6273531/500000000000000000000 : ℝ)*base92 + (6273531/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1040_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1040_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1040_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1040_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1040_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
