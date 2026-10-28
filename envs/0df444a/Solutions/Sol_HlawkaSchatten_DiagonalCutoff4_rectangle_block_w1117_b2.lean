-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:04.050234+00:00
-- url     : https://prove2.me/submissions/340b226b-2e10-458d-949c-a78dabb1daac

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
theorem support_rectangle_w1117_s6_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178862407/10000000000 : ℝ)*x 0 + (5393885447/10000000000 : ℝ)*x 1 + (658118521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178862407/10000000000 : ℝ)^4155 ≤ (529488451023/4000000000000 : ℝ)^3131 := by
    have hnat : (2178862407 : ℕ)^4155*4000000000000^3131 ≤ 529488451023^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178862407 10000000000 529488451023 4000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393885447/10000000000 : ℝ)^4155 ≤ (2754860684079/6250000000000 : ℝ)^3131 := by
    have hnat : (5393885447 : ℕ)^4155*6250000000000^3131 ≤ 2754860684079^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393885447 10000000000 2754860684079 6250000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658118521/1250000000 : ℝ)^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131 := by
    have hnat : (658118521 : ℕ)^4155*100000000000000^3131 ≤ 42685017764837^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658118521 1250000000 42685017764837 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178862407/10000000000 : ℝ), (5393885447/10000000000 : ℝ), (658118521/1250000000 : ℝ)] ![(529488451023/4000000000000 : ℝ), (2754860684079/6250000000000 : ℝ), (42685017764837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178862407/10000000000 : ℝ)|^4155 ≤ (529488451023/4000000000000 : ℝ)^3131
        have hw : |(-2178862407/10000000000 : ℝ)|=(2178862407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393885447/10000000000 : ℝ)|^4155 ≤ (2754860684079/6250000000000 : ℝ)^3131
        have hw : |(5393885447/10000000000 : ℝ)|=(5393885447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658118521/1250000000 : ℝ)|^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131
        have hw : |(658118521/1250000000 : ℝ)|=(658118521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672472903/5000000000 : ℝ)*x 0 + (-2244273759/10000000000 : ℝ)*x 1 + (658118521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672472903/5000000000 : ℝ)^4155 ≤ (43547838530439/100000000000000 : ℝ)^3131 := by
    have hnat : (2672472903 : ℕ)^4155*100000000000000^3131 ≤ 43547838530439^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672472903 5000000000 43547838530439 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244273759/10000000000 : ℝ)^4155 ≤ (13767143695909/100000000000000 : ℝ)^3131 := by
    have hnat : (2244273759 : ℕ)^4155*100000000000000^3131 ≤ 13767143695909^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244273759 10000000000 13767143695909 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658118521/1250000000 : ℝ)^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131 := by
    have hnat : (658118521 : ℕ)^4155*100000000000000^3131 ≤ 42685017764837^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658118521 1250000000 42685017764837 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672472903/5000000000 : ℝ), (-2244273759/10000000000 : ℝ), (658118521/1250000000 : ℝ)] ![(43547838530439/100000000000000 : ℝ), (13767143695909/100000000000000 : ℝ), (42685017764837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672472903/5000000000 : ℝ)|^4155 ≤ (43547838530439/100000000000000 : ℝ)^3131
        have hw : |(2672472903/5000000000 : ℝ)|=(2672472903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244273759/10000000000 : ℝ)|^4155 ≤ (13767143695909/100000000000000 : ℝ)^3131
        have hw : |(-2244273759/10000000000 : ℝ)|=(2244273759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658118521/1250000000 : ℝ)|^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131
        have hw : |(658118521/1250000000 : ℝ)|=(658118521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672472903/5000000000 : ℝ)*x 0 + (658118521/1250000000 : ℝ)*x 1 + (-2244273759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672472903/5000000000 : ℝ)^4155 ≤ (43547838530439/100000000000000 : ℝ)^3131 := by
    have hnat : (2672472903 : ℕ)^4155*100000000000000^3131 ≤ 43547838530439^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672472903 5000000000 43547838530439 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658118521/1250000000 : ℝ)^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131 := by
    have hnat : (658118521 : ℕ)^4155*100000000000000^3131 ≤ 42685017764837^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658118521 1250000000 42685017764837 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244273759/10000000000 : ℝ)^4155 ≤ (13767143695909/100000000000000 : ℝ)^3131 := by
    have hnat : (2244273759 : ℕ)^4155*100000000000000^3131 ≤ 13767143695909^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244273759 10000000000 13767143695909 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672472903/5000000000 : ℝ), (658118521/1250000000 : ℝ), (-2244273759/10000000000 : ℝ)] ![(43547838530439/100000000000000 : ℝ), (42685017764837/100000000000000 : ℝ), (13767143695909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672472903/5000000000 : ℝ)|^4155 ≤ (43547838530439/100000000000000 : ℝ)^3131
        have hw : |(2672472903/5000000000 : ℝ)|=(2672472903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658118521/1250000000 : ℝ)|^4155 ≤ (42685017764837/100000000000000 : ℝ)^3131
        have hw : |(658118521/1250000000 : ℝ)|=(658118521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244273759/10000000000 : ℝ)|^4155 ≤ (13767143695909/100000000000000 : ℝ)^3131
        have hw : |(-2244273759/10000000000 : ℝ)|=(2244273759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273011691/625000000 : ℝ)*x 0 + (4242423301/10000000000 : ℝ)*x 1 + (4497683429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273011691/625000000 : ℝ)^4155 ≤ (16658312595849/50000000000000 : ℝ)^3131 := by
    have hnat : (273011691 : ℕ)^4155*50000000000000^3131 ≤ 16658312595849^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273011691 625000000 16658312595849 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242423301/10000000000 : ℝ)^4155 ≤ (32049731152109/100000000000000 : ℝ)^3131 := by
    have hnat : (4242423301 : ℕ)^4155*100000000000000^3131 ≤ 32049731152109^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242423301 10000000000 32049731152109 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497683429/10000000000 : ℝ)^4155 ≤ (34633643634577/100000000000000 : ℝ)^3131 := by
    have hnat : (4497683429 : ℕ)^4155*100000000000000^3131 ≤ 34633643634577^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497683429 10000000000 34633643634577 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273011691/625000000 : ℝ), (4242423301/10000000000 : ℝ), (4497683429/10000000000 : ℝ)] ![(16658312595849/50000000000000 : ℝ), (32049731152109/100000000000000 : ℝ), (34633643634577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273011691/625000000 : ℝ)|^4155 ≤ (16658312595849/50000000000000 : ℝ)^3131
        have hw : |(273011691/625000000 : ℝ)|=(273011691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242423301/10000000000 : ℝ)|^4155 ≤ (32049731152109/100000000000000 : ℝ)^3131
        have hw : |(4242423301/10000000000 : ℝ)|=(4242423301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497683429/10000000000 : ℝ)|^4155 ≤ (34633643634577/100000000000000 : ℝ)^3131
        have hw : |(4497683429/10000000000 : ℝ)|=(4497683429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178867459/10000000000 : ℝ)*x 0 + (1316318439/2500000000 : ℝ)*x 1 + (5393558663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178867459/10000000000 : ℝ)^4155 ≤ (13237252005927/100000000000000 : ℝ)^3131 := by
    have hnat : (2178867459 : ℕ)^4155*100000000000000^3131 ≤ 13237252005927^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178867459 10000000000 13237252005927 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316318439/2500000000 : ℝ)^4155 ≤ (21344260390369/50000000000000 : ℝ)^3131 := by
    have hnat : (1316318439 : ℕ)^4155*50000000000000^3131 ≤ 21344260390369^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316318439 2500000000 21344260390369 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393558663/10000000000 : ℝ)^4155 ≤ (44074227201213/100000000000000 : ℝ)^3131 := by
    have hnat : (5393558663 : ℕ)^4155*100000000000000^3131 ≤ 44074227201213^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393558663 10000000000 44074227201213 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178867459/10000000000 : ℝ), (1316318439/2500000000 : ℝ), (5393558663/10000000000 : ℝ)] ![(13237252005927/100000000000000 : ℝ), (21344260390369/50000000000000 : ℝ), (44074227201213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178867459/10000000000 : ℝ)|^4155 ≤ (13237252005927/100000000000000 : ℝ)^3131
        have hw : |(-2178867459/10000000000 : ℝ)|=(2178867459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316318439/2500000000 : ℝ)|^4155 ≤ (21344260390369/50000000000000 : ℝ)^3131
        have hw : |(1316318439/2500000000 : ℝ)|=(1316318439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393558663/10000000000 : ℝ)|^4155 ≤ (44074227201213/100000000000000 : ℝ)^3131
        have hw : |(5393558663/10000000000 : ℝ)|=(5393558663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531234019/1000000000 : ℝ)*x 0 + (-1057831633/5000000000 : ℝ)*x 1 + (1078711727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531234019/1000000000 : ℝ)^4155 ≤ (2699728407993/6250000000000 : ℝ)^3131 := by
    have hnat : (531234019 : ℕ)^4155*6250000000000^3131 ≤ 2699728407993^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531234019 1000000000 2699728407993 6250000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057831633/5000000000 : ℝ)^4155 ≤ (2546023713261/20000000000000 : ℝ)^3131 := by
    have hnat : (1057831633 : ℕ)^4155*20000000000000^3131 ≤ 2546023713261^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057831633 5000000000 2546023713261 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078711727/2000000000 : ℝ)^4155 ≤ (5509278362197/12500000000000 : ℝ)^3131 := by
    have hnat : (1078711727 : ℕ)^4155*12500000000000^3131 ≤ 5509278362197^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078711727 2000000000 5509278362197 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531234019/1000000000 : ℝ), (-1057831633/5000000000 : ℝ), (1078711727/2000000000 : ℝ)] ![(2699728407993/6250000000000 : ℝ), (2546023713261/20000000000000 : ℝ), (5509278362197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531234019/1000000000 : ℝ)|^4155 ≤ (2699728407993/6250000000000 : ℝ)^3131
        have hw : |(531234019/1000000000 : ℝ)|=(531234019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057831633/5000000000 : ℝ)|^4155 ≤ (2546023713261/20000000000000 : ℝ)^3131
        have hw : |(-1057831633/5000000000 : ℝ)|=(1057831633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078711727/2000000000 : ℝ)|^4155 ≤ (5509278362197/12500000000000 : ℝ)^3131
        have hw : |(1078711727/2000000000 : ℝ)|=(1078711727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265617011/500000000 : ℝ)*x 0 + (5393558593/10000000000 : ℝ)*x 1 + (-1057831641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265617011/500000000 : ℝ)^4155 ≤ (10798913712901/25000000000000 : ℝ)^3131 := by
    have hnat : (265617011 : ℕ)^4155*25000000000000^3131 ≤ 10798913712901^3131*500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265617011 500000000 10798913712901 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393558593/10000000000 : ℝ)^4155 ≤ (1101855661053/2500000000000 : ℝ)^3131 := by
    have hnat : (5393558593 : ℕ)^4155*2500000000000^3131 ≤ 1101855661053^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393558593 10000000000 1101855661053 2500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057831641/5000000000 : ℝ)^4155 ≤ (2546023738813/20000000000000 : ℝ)^3131 := by
    have hnat : (1057831641 : ℕ)^4155*20000000000000^3131 ≤ 2546023738813^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057831641 5000000000 2546023738813 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265617011/500000000 : ℝ), (5393558593/10000000000 : ℝ), (-1057831641/5000000000 : ℝ)] ![(10798913712901/25000000000000 : ℝ), (1101855661053/2500000000000 : ℝ), (2546023738813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265617011/500000000 : ℝ)|^4155 ≤ (10798913712901/25000000000000 : ℝ)^3131
        have hw : |(265617011/500000000 : ℝ)|=(265617011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393558593/10000000000 : ℝ)|^4155 ≤ (1101855661053/2500000000000 : ℝ)^3131
        have hw : |(5393558593/10000000000 : ℝ)|=(5393558593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057831641/5000000000 : ℝ)|^4155 ≤ (2546023738813/20000000000000 : ℝ)^3131
        have hw : |(-1057831641/5000000000 : ℝ)|=(1057831641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s6_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092049257/2500000000 : ℝ)*x 0 + (4497038781/10000000000 : ℝ)*x 1 + (265191893/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092049257/2500000000 : ℝ)^4155 ≤ (33316726123997/100000000000000 : ℝ)^3131 := by
    have hnat : (1092049257 : ℕ)^4155*100000000000000^3131 ≤ 33316726123997^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092049257 2500000000 33316726123997 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497038781/10000000000 : ℝ)^4155 ≤ (8656764075007/25000000000000 : ℝ)^3131 := by
    have hnat : (4497038781 : ℕ)^4155*25000000000000^3131 ≤ 8656764075007^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497038781 10000000000 8656764075007 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265191893/625000000 : ℝ)^4155 ≤ (6411243513437/20000000000000 : ℝ)^3131 := by
    have hnat : (265191893 : ℕ)^4155*20000000000000^3131 ≤ 6411243513437^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265191893 625000000 6411243513437 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092049257/2500000000 : ℝ), (4497038781/10000000000 : ℝ), (265191893/625000000 : ℝ)] ![(33316726123997/100000000000000 : ℝ), (8656764075007/25000000000000 : ℝ), (6411243513437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092049257/2500000000 : ℝ)|^4155 ≤ (33316726123997/100000000000000 : ℝ)^3131
        have hw : |(1092049257/2500000000 : ℝ)|=(1092049257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497038781/10000000000 : ℝ)|^4155 ≤ (8656764075007/25000000000000 : ℝ)^3131
        have hw : |(4497038781/10000000000 : ℝ)|=(4497038781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265191893/625000000 : ℝ)|^4155 ≤ (6411243513437/20000000000000 : ℝ)^3131
        have hw : |(265191893/625000000 : ℝ)|=(265191893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5639/50000 : ℝ) ^ (8309/2048 : ℝ) ≤ (3570453863621953/25000000000000000000 : ℝ) := by
    have hpowers : (5639/50000 : ℝ)^8309 ≤ (3570453863621953/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5639 : ℕ)^8309*25000000000000000000^2048 ≤ 3570453863621953^2048*50000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5639 50000 3570453863621953 25000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5639/50000 : ℝ)) (X := (3570453863621953/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (8781851381281441/25000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^8309 ≤ (8781851381281441/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14079 : ℕ)^8309*25000000000000000000^2048 ≤ 8781851381281441^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 8781851381281441 25000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (8781851381281441/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503570453863621953/12500000000000000000 : ℝ) ≤ (2000140791964799/2000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12503570453863621953/12500000000000000000 : ℝ)^2048 ≤ (2000140791964799/2000000000000000 : ℝ)^8309 := by
      have hnat : (12503570453863621953 : ℕ)^2048*2000000000000000^8309 ≤ 2000140791964799^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503570453863621953 12500000000000000000 2000140791964799 2000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000140791964799/2000000000000000 : ℝ)) (X := (12503570453863621953/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506176152622451697/12500000000000000000 : ℝ) ≤ (625076100653689/625000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12506176152622451697/12500000000000000000 : ℝ)^2048 ≤ (625076100653689/625000000000000 : ℝ)^8309 := by
      have hnat : (12506176152622451697 : ℕ)^2048*625000000000000^8309 ≤ 625076100653689^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506176152622451697 12500000000000000000 625076100653689 625000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625076100653689/625000000000000 : ℝ)) (X := (12506176152622451697/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508781851381281441/12500000000000000000 : ℝ) ≤ (10001731261094053/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12508781851381281441/12500000000000000000 : ℝ)^2048 ≤ (10001731261094053/10000000000000000 : ℝ)^8309 := by
      have hnat : (12508781851381281441 : ℕ)^2048*10000000000000000^8309 ≤ 10001731261094053^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508781851381281441 12500000000000000000 10001731261094053 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001731261094053/10000000000000000 : ℝ)) (X := (12508781851381281441/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3570453863621953/25000000000000000000 : ℝ) ≤ ((28000385887743295871/28010000000000000000 : ℝ)+2*(513650635029/280100000000000 : ℝ)*(5639/50000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (28000385887743295871/28010000000000000000 : ℝ)+2*(513650635029/280100000000000 : ℝ)*(5639/50000 : ℝ)=(2000140791964799/2000000000000000 : ℝ) by norm_num, show 1+2*(3570453863621953/25000000000000000000 : ℝ)=(12503570453863621953/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8781851381281441/25000000000000000000 : ℝ)+(3570453863621953/25000000000000000000 : ℝ) ≤ ((28000385887743295871/28010000000000000000 : ℝ)+(513650635029/280100000000000 : ℝ)*((14079/100000 : ℝ)+(5639/50000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (28000385887743295871/28010000000000000000 : ℝ)+(513650635029/280100000000000 : ℝ)*((14079/100000 : ℝ)+(5639/50000 : ℝ))=(625076100653689/625000000000000 : ℝ) by norm_num, show 1+(8781851381281441/25000000000000000000 : ℝ)+(3570453863621953/25000000000000000000 : ℝ)=(12506176152622451697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8781851381281441/25000000000000000000 : ℝ) ≤ ((28000385887743295871/28010000000000000000 : ℝ)+2*(513650635029/280100000000000 : ℝ)*(14079/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (28000385887743295871/28010000000000000000 : ℝ)+2*(513650635029/280100000000000 : ℝ)*(14079/100000 : ℝ)=(10001731261094053/10000000000000000 : ℝ) by norm_num, show 1+2*(8781851381281441/25000000000000000000 : ℝ)=(12508781851381281441/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28000385887743295871/28010000000000000000 : ℝ)*(X 1 0+X 2 0)+(513650635029/280100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (28000385887743295871/28010000000000000000 : ℝ)) (alpha := (513650635029/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28000385887743295871/28010000000000000000 : ℝ)*(X 0 1+X 2 1)+(513650635029/280100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (28000385887743295871/28010000000000000000 : ℝ)) (alpha := (513650635029/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28000385887743295871/28010000000000000000 : ℝ)*(X 0 2+X 1 2)+(513650635029/280100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (28000385887743295871/28010000000000000000 : ℝ)) (alpha := (513650635029/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2178862407/10000000000 : ℝ)*X 0 0+(5393885447/10000000000 : ℝ)*X 0 1+(658118521/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672472903/5000000000 : ℝ)*X 1 0+(-2244273759/10000000000 : ℝ)*X 1 1+(658118521/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672472903/5000000000 : ℝ)*X 2 0+(658118521/1250000000 : ℝ)*X 2 1+(-2244273759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273011691/625000000 : ℝ)*X 0 0+(4242423301/10000000000 : ℝ)*X 0 1+(4497683429/10000000000 : ℝ)*X 0 2+(273011691/625000000 : ℝ)*X 1 0+(4242423301/10000000000 : ℝ)*X 1 1+(4497683429/10000000000 : ℝ)*X 1 2+(273011691/625000000 : ℝ)*X 2 0+(4242423301/10000000000 : ℝ)*X 2 1+(4497683429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2178867459/10000000000 : ℝ)*X 0 0+(1316318439/2500000000 : ℝ)*X 0 1+(5393558663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531234019/1000000000 : ℝ)*X 1 0+(-1057831633/5000000000 : ℝ)*X 1 1+(1078711727/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265617011/500000000 : ℝ)*X 2 0+(5393558593/10000000000 : ℝ)*X 2 1+(-1057831641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092049257/2500000000 : ℝ)*X 0 0+(4497038781/10000000000 : ℝ)*X 0 1+(265191893/625000000 : ℝ)*X 0 2+(1092049257/2500000000 : ℝ)*X 1 0+(4497038781/10000000000 : ℝ)*X 1 1+(265191893/625000000 : ℝ)*X 1 2+(1092049257/2500000000 : ℝ)*X 2 0+(4497038781/10000000000 : ℝ)*X 2 1+(265191893/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1809312611178950173086743277/280100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20087551/1562500000000 : ℝ)*(base19) + (119705537/10000000000000 : ℝ)*(base23) + (47328369/100000000000000 : ℝ)*(lower2) + (163942941/100000000000000 : ℝ)*(upper3) + (24557049/25000000000000 : ℝ)*(upper5) + (1167338810592529/20000000000000 : ℝ)*(major0) + (1167338810592529/20000000000000 : ℝ)*(major1) + (1167338810592529/20000000000000 : ℝ)*(major2) + (7755745136958113/100000000000000 : ℝ)*(sp0) + (969472304519777/12500000000000 : ℝ)*(sp1) + (775577852470611/10000000000000 : ℝ)*(sp2) + (3917589275455637/100000000000000 : ℝ)*(sp3) + (4323100421/12500000000000 : ℝ)*(sp4) + (3778678141/20000000000000 : ℝ)*(sp7) + (1958804084423171/50000000000000 : ℝ)*(f.failure) + (7755779721761481/100000000000000 : ℝ)*(f.sum) + (27582610989/5470703125000000000000000 : ℝ)*base66 + (1380725207468952241/560200000000000000000000000000000 : ℝ)*base68 + (1237001878087047759/560200000000000000000000000000000 : ℝ)*base69 + (2291712054078352241/560200000000000000000000000000000 : ℝ)*base72 + (12324255309543/2801000000000000000000000000 : ℝ)*base73 + (4302817202023047759/560200000000000000000000000000000 : ℝ)*base75 + (4905287376431152241/560200000000000000000000000000000 : ℝ)*base78 + (861316036581152241/560200000000000000000000000000000 : ℝ)*base80 + (1637153574559/1400500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9420149/2500000000000000000000 : ℝ)*base90 + (9420149/2500000000000000000000 : ℝ)*base92 + (9420149/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278975046973319507857773327/56020000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42972007/4000000000000 : ℝ)*(base19) + (36214127/3125000000000 : ℝ)*(base23) + (87764113/100000000000000 : ℝ)*(upper3) + (4988609/20000000000000 : ℝ)*(lower4) + (25868661/20000000000000 : ℝ)*(upper5) + (234652931016379/4000000000000 : ℝ)*(major0) + (234652931016379/4000000000000 : ℝ)*(major1) + (234652931016379/4000000000000 : ℝ)*(major2) + (29957090429/100000000000000 : ℝ)*(sp1) + (1806923571/6250000000000 : ℝ)*(sp2) + (7795150984806257/100000000000000 : ℝ)*(sp4) + (7795119953415653/100000000000000 : ℝ)*(sp5) + (3897560457588529/50000000000000 : ℝ)*(sp6) + (984373850003847/25000000000000 : ℝ)*(sp7) + (984373850003847/25000000000000 : ℝ)*(f.failure) + (7795150984806257/100000000000000 : ℝ)*(f.sum) + (5761699600627/1400500000000000000000000000 : ℝ)*base65 + (1376630332629628891/112040000000000000000000000000000 : ℝ)*base68 + (318893499622228891/112040000000000000000000000000000 : ℝ)*base70 + (214068951978851109/112040000000000000000000000000000 : ℝ)*base71 + (1804193845009/700250000000000000000000000 : ℝ)*base73 + (2216542242987668891/112040000000000000000000000000000 : ℝ)*base76 + (746787833213571109/112040000000000000000000000000000 : ℝ)*base77 + (2856135893227628891/112040000000000000000000000000000 : ℝ)*base80 + (15486093607591/2801000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (12617393/1250000000000000000000 : ℝ)*base90 + (12617393/1250000000000000000000 : ℝ)*base92 + (12617393/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s7_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178895363/10000000000 : ℝ)*x 0 + (674190033/1250000000 : ℝ)*x 1 + (5265291549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178895363/10000000000 : ℝ)^4155 ≤ (13237476974761/100000000000000 : ℝ)^3131 := by
    have hnat : (2178895363 : ℕ)^4155*100000000000000^3131 ≤ 13237476974761^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178895363 10000000000 13237476974761 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674190033/1250000000 : ℝ)^4155 ≤ (44073810795511/100000000000000 : ℝ)^3131 := by
    have hnat : (674190033 : ℕ)^4155*100000000000000^3131 ≤ 44073810795511^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674190033 1250000000 44073810795511 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265291549/10000000000 : ℝ)^4155 ≤ (8537742443693/20000000000000 : ℝ)^3131 := by
    have hnat : (5265291549 : ℕ)^4155*20000000000000^3131 ≤ 8537742443693^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265291549 10000000000 8537742443693 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178895363/10000000000 : ℝ), (674190033/1250000000 : ℝ), (5265291549/10000000000 : ℝ)] ![(13237476974761/100000000000000 : ℝ), (44073810795511/100000000000000 : ℝ), (8537742443693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178895363/10000000000 : ℝ)|^4155 ≤ (13237476974761/100000000000000 : ℝ)^3131
        have hw : |(-2178895363/10000000000 : ℝ)|=(2178895363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674190033/1250000000 : ℝ)|^4155 ≤ (44073810795511/100000000000000 : ℝ)^3131
        have hw : |(674190033/1250000000 : ℝ)|=(674190033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265291549/10000000000 : ℝ)|^4155 ≤ (8537742443693/20000000000000 : ℝ)^3131
        have hw : |(5265291549/10000000000 : ℝ)|=(5265291549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334053363/625000000 : ℝ)*x 0 + (-448788421/2000000000 : ℝ)*x 1 + (5265291551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334053363/625000000 : ℝ)^4155 ≤ (5443355479863/12500000000000 : ℝ)^3131 := by
    have hnat : (334053363 : ℕ)^4155*12500000000000^3131 ≤ 5443355479863^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334053363 625000000 5443355479863 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448788421/2000000000 : ℝ)^4155 ≤ (2752888780269/20000000000000 : ℝ)^3131 := by
    have hnat : (448788421 : ℕ)^4155*20000000000000^3131 ≤ 2752888780269^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448788421 2000000000 2752888780269 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265291551/10000000000 : ℝ)^4155 ≤ (42688712239983/100000000000000 : ℝ)^3131 := by
    have hnat : (5265291551 : ℕ)^4155*100000000000000^3131 ≤ 42688712239983^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265291551 10000000000 42688712239983 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334053363/625000000 : ℝ), (-448788421/2000000000 : ℝ), (5265291551/10000000000 : ℝ)] ![(5443355479863/12500000000000 : ℝ), (2752888780269/20000000000000 : ℝ), (42688712239983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334053363/625000000 : ℝ)|^4155 ≤ (5443355479863/12500000000000 : ℝ)^3131
        have hw : |(334053363/625000000 : ℝ)|=(334053363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448788421/2000000000 : ℝ)|^4155 ≤ (2752888780269/20000000000000 : ℝ)^3131
        have hw : |(-448788421/2000000000 : ℝ)|=(448788421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265291551/10000000000 : ℝ)|^4155 ≤ (42688712239983/100000000000000 : ℝ)^3131
        have hw : |(5265291551/10000000000 : ℝ)|=(5265291551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344853809/10000000000 : ℝ)*x 0 + (164540361/312500000 : ℝ)*x 1 + (-2243942103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344853809/10000000000 : ℝ)^4155 ≤ (10886710962429/25000000000000 : ℝ)^3131 := by
    have hnat : (5344853809 : ℕ)^4155*25000000000000^3131 ≤ 10886710962429^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344853809 10000000000 10886710962429 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164540361/312500000 : ℝ)^4155 ≤ (42688712250743/100000000000000 : ℝ)^3131 := by
    have hnat : (164540361 : ℕ)^4155*100000000000000^3131 ≤ 42688712250743^3131*312500000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164540361 312500000 42688712250743 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243942103/10000000000 : ℝ)^4155 ≤ (2752888777013/20000000000000 : ℝ)^3131 := by
    have hnat : (2243942103 : ℕ)^4155*20000000000000^3131 ≤ 2752888777013^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243942103 10000000000 2752888777013 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344853809/10000000000 : ℝ), (164540361/312500000 : ℝ), (-2243942103/10000000000 : ℝ)] ![(10886710962429/25000000000000 : ℝ), (42688712250743/100000000000000 : ℝ), (2752888777013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344853809/10000000000 : ℝ)|^4155 ≤ (10886710962429/25000000000000 : ℝ)^3131
        have hw : |(5344853809/10000000000 : ℝ)|=(5344853809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164540361/312500000 : ℝ)|^4155 ≤ (42688712250743/100000000000000 : ℝ)^3131
        have hw : |(164540361/312500000 : ℝ)|=(164540361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243942103/10000000000 : ℝ)|^4155 ≤ (2752888777013/20000000000000 : ℝ)^3131
        have hw : |(-2243942103/10000000000 : ℝ)|=(2243942103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184102569/5000000000 : ℝ)*x 0 + (4243122331/10000000000 : ℝ)*x 1 + (1124244921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184102569/5000000000 : ℝ)^4155 ≤ (8329202052497/25000000000000 : ℝ)^3131 := by
    have hnat : (2184102569 : ℕ)^4155*25000000000000^3131 ≤ 8329202052497^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184102569 5000000000 8329202052497 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243122331/10000000000 : ℝ)^4155 ≤ (1001773104441/3125000000000 : ℝ)^3131 := by
    have hnat : (4243122331 : ℕ)^4155*3125000000000^3131 ≤ 1001773104441^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243122331 10000000000 1001773104441 3125000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124244921/2500000000 : ℝ)^4155 ≤ (34626452432881/100000000000000 : ℝ)^3131 := by
    have hnat : (1124244921 : ℕ)^4155*100000000000000^3131 ≤ 34626452432881^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124244921 2500000000 34626452432881 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184102569/5000000000 : ℝ), (4243122331/10000000000 : ℝ), (1124244921/2500000000 : ℝ)] ![(8329202052497/25000000000000 : ℝ), (1001773104441/3125000000000 : ℝ), (34626452432881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184102569/5000000000 : ℝ)|^4155 ≤ (8329202052497/25000000000000 : ℝ)^3131
        have hw : |(2184102569/5000000000 : ℝ)|=(2184102569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243122331/10000000000 : ℝ)|^4155 ≤ (1001773104441/3125000000000 : ℝ)^3131
        have hw : |(4243122331/10000000000 : ℝ)|=(4243122331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124244921/2500000000 : ℝ)|^4155 ≤ (34626452432881/100000000000000 : ℝ)^3131
        have hw : |(1124244921/2500000000 : ℝ)|=(1124244921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178900311/10000000000 : ℝ)*x 0 + (5265613541/10000000000 : ℝ)*x 1 + (5393197111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178900311/10000000000 : ℝ)^4155 ≤ (13237516866839/100000000000000 : ℝ)^3131 := by
    have hnat : (2178900311 : ℕ)^4155*100000000000000^3131 ≤ 13237516866839^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178900311 10000000000 13237516866839 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265613541/10000000000 : ℝ)^4155 ≤ (21346088309173/50000000000000 : ℝ)^3131 := by
    have hnat : (5265613541 : ℕ)^4155*50000000000000^3131 ≤ 21346088309173^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265613541 10000000000 21346088309173 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393197111/10000000000 : ℝ)^4155 ≤ (4407030650433/10000000000000 : ℝ)^3131 := by
    have hnat : (5393197111 : ℕ)^4155*10000000000000^3131 ≤ 4407030650433^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393197111 10000000000 4407030650433 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178900311/10000000000 : ℝ), (5265613541/10000000000 : ℝ), (5393197111/10000000000 : ℝ)] ![(13237516866839/100000000000000 : ℝ), (21346088309173/50000000000000 : ℝ), (4407030650433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178900311/10000000000 : ℝ)|^4155 ≤ (13237516866839/100000000000000 : ℝ)^3131
        have hw : |(-2178900311/10000000000 : ℝ)|=(2178900311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265613541/10000000000 : ℝ)|^4155 ≤ (21346088309173/50000000000000 : ℝ)^3131
        have hw : |(5265613541/10000000000 : ℝ)|=(5265613541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393197111/10000000000 : ℝ)|^4155 ≤ (4407030650433/10000000000000 : ℝ)^3131
        have hw : |(5393197111/10000000000 : ℝ)|=(5393197111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312427277/10000000000 : ℝ)*x 0 + (-2116036539/10000000000 : ℝ)*x 1 + (674149639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312427277/10000000000 : ℝ)^4155 ≤ (43196594243919/100000000000000 : ℝ)^3131 := by
    have hnat : (5312427277 : ℕ)^4155*100000000000000^3131 ≤ 43196594243919^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312427277 10000000000 43196594243919 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116036539/10000000000 : ℝ)^4155 ≤ (12733099229947/100000000000000 : ℝ)^3131 := by
    have hnat : (2116036539 : ℕ)^4155*100000000000000^3131 ≤ 12733099229947^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116036539 10000000000 12733099229947 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674149639/1250000000 : ℝ)^4155 ≤ (22035153257587/50000000000000 : ℝ)^3131 := by
    have hnat : (674149639 : ℕ)^4155*50000000000000^3131 ≤ 22035153257587^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674149639 1250000000 22035153257587 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312427277/10000000000 : ℝ), (-2116036539/10000000000 : ℝ), (674149639/1250000000 : ℝ)] ![(43196594243919/100000000000000 : ℝ), (12733099229947/100000000000000 : ℝ), (22035153257587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312427277/10000000000 : ℝ)|^4155 ≤ (43196594243919/100000000000000 : ℝ)^3131
        have hw : |(5312427277/10000000000 : ℝ)|=(5312427277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116036539/10000000000 : ℝ)|^4155 ≤ (12733099229947/100000000000000 : ℝ)^3131
        have hw : |(-2116036539/10000000000 : ℝ)|=(2116036539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674149639/1250000000 : ℝ)|^4155 ≤ (22035153257587/50000000000000 : ℝ)^3131
        have hw : |(674149639/1250000000 : ℝ)|=(674149639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531242727/1000000000 : ℝ)*x 0 + (674149639/1250000000 : ℝ)*x 1 + (-529009137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531242727/1000000000 : ℝ)^4155 ≤ (8639318833677/20000000000000 : ℝ)^3131 := by
    have hnat : (531242727 : ℕ)^4155*20000000000000^3131 ≤ 8639318833677^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531242727 1000000000 8639318833677 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674149639/1250000000 : ℝ)^4155 ≤ (22035153257587/50000000000000 : ℝ)^3131 := by
    have hnat : (674149639 : ℕ)^4155*50000000000000^3131 ≤ 22035153257587^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674149639 1250000000 22035153257587 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529009137/2500000000 : ℝ)^4155 ≤ (1591637412727/12500000000000 : ℝ)^3131 := by
    have hnat : (529009137 : ℕ)^4155*12500000000000^3131 ≤ 1591637412727^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529009137 2500000000 1591637412727 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531242727/1000000000 : ℝ), (674149639/1250000000 : ℝ), (-529009137/2500000000 : ℝ)] ![(8639318833677/20000000000000 : ℝ), (22035153257587/50000000000000 : ℝ), (1591637412727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531242727/1000000000 : ℝ)|^4155 ≤ (8639318833677/20000000000000 : ℝ)^3131
        have hw : |(531242727/1000000000 : ℝ)|=(531242727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674149639/1250000000 : ℝ)|^4155 ≤ (22035153257587/50000000000000 : ℝ)^3131
        have hw : |(674149639/1250000000 : ℝ)|=(674149639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529009137/2500000000 : ℝ)|^4155 ≤ (1591637412727/12500000000000 : ℝ)^3131
        have hw : |(-529009137/2500000000 : ℝ)|=(529009137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s7_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136506717/312500000 : ℝ)*x 0 + (899268449/2000000000 : ℝ)*x 1 + (4243762069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136506717/312500000 : ℝ)^4155 ≤ (33316907462241/100000000000000 : ℝ)^3131 := by
    have hnat : (136506717 : ℕ)^4155*100000000000000^3131 ≤ 33316907462241^3131*312500000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136506717 312500000 33316907462241 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899268449/2000000000 : ℝ)^4155 ≤ (17309969547573/50000000000000 : ℝ)^3131 := by
    have hnat : (899268449 : ℕ)^4155*50000000000000^3131 ≤ 17309969547573^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899268449 2000000000 17309969547573 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243762069/10000000000 : ℝ)^4155 ≤ (8015788356401/25000000000000 : ℝ)^3131 := by
    have hnat : (4243762069 : ℕ)^4155*25000000000000^3131 ≤ 8015788356401^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243762069 10000000000 8015788356401 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136506717/312500000 : ℝ), (899268449/2000000000 : ℝ), (4243762069/10000000000 : ℝ)] ![(33316907462241/100000000000000 : ℝ), (17309969547573/50000000000000 : ℝ), (8015788356401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136506717/312500000 : ℝ)|^4155 ≤ (33316907462241/100000000000000 : ℝ)^3131
        have hw : |(136506717/312500000 : ℝ)|=(136506717/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899268449/2000000000 : ℝ)|^4155 ≤ (17309969547573/50000000000000 : ℝ)^3131
        have hw : |(899268449/2000000000 : ℝ)|=(899268449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243762069/10000000000 : ℝ)|^4155 ≤ (8015788356401/25000000000000 : ℝ)^3131
        have hw : |(4243762069/10000000000 : ℝ)|=(4243762069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11319/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (707/6250 : ℝ) ^ (8309/2048 : ℝ) ≤ (14457304449625643/100000000000000000000 : ℝ) := by
    have hpowers : (707/6250 : ℝ)^8309 ≤ (14457304449625643/100000000000000000000 : ℝ)^2048 := by
      have hnat : (707 : ℕ)^8309*100000000000000000000^2048 ≤ 14457304449625643^2048*6250^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 6250 14457304449625643 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/6250 : ℝ)) (X := (14457304449625643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (34764412921452471/100000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^8309 ≤ (34764412921452471/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14043 : ℕ)^8309*100000000000000000000^2048 ≤ 34764412921452471^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 34764412921452471 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (34764412921452471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014457304449625643/50000000000000000000 : ℝ) ≤ (400028504353871/400000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50014457304449625643/50000000000000000000 : ℝ)^2048 ≤ (400028504353871/400000000000000 : ℝ)^8309 := by
      have hnat : (50014457304449625643 : ℕ)^2048*400000000000000^8309 ≤ 400028504353871^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014457304449625643 50000000000000000000 400028504353871 400000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400028504353871/400000000000000 : ℝ)) (X := (50014457304449625643/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024610858685539057/50000000000000000000 : ℝ) ≤ (2500303247647991/2500000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50024610858685539057/50000000000000000000 : ℝ)^2048 ≤ (2500303247647991/2500000000000000 : ℝ)^8309 := by
      have hnat : (50024610858685539057 : ℕ)^2048*2500000000000000^8309 ≤ 2500303247647991^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024610858685539057 50000000000000000000 2500303247647991 2500000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500303247647991/2500000000000000 : ℝ)) (X := (50024610858685539057/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034764412921452471/50000000000000000000 : ℝ) ≤ (10001713372337153/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50034764412921452471/50000000000000000000 : ℝ)^2048 ≤ (10001713372337153/10000000000000000 : ℝ)^8309 := by
      have hnat : (50034764412921452471 : ℕ)^2048*10000000000000000^8309 ≤ 10001713372337153^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034764412921452471 50000000000000000000 10001713372337153 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001713372337153/10000000000000000 : ℝ)) (X := (50034764412921452471/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14457304449625643/100000000000000000000 : ℝ) ≤ ((27300625498157386589/27310000000000000000 : ℝ)+2*(500381745189/273100000000000 : ℝ)*(707/6250 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (27300625498157386589/27310000000000000000 : ℝ)+2*(500381745189/273100000000000 : ℝ)*(707/6250 : ℝ)=(400028504353871/400000000000000 : ℝ) by norm_num, show 1+2*(14457304449625643/100000000000000000000 : ℝ)=(50014457304449625643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34764412921452471/100000000000000000000 : ℝ)+(14457304449625643/100000000000000000000 : ℝ) ≤ ((27300625498157386589/27310000000000000000 : ℝ)+(500381745189/273100000000000 : ℝ)*((14043/100000 : ℝ)+(707/6250 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (27300625498157386589/27310000000000000000 : ℝ)+(500381745189/273100000000000 : ℝ)*((14043/100000 : ℝ)+(707/6250 : ℝ))=(2500303247647991/2500000000000000 : ℝ) by norm_num, show 1+(34764412921452471/100000000000000000000 : ℝ)+(14457304449625643/100000000000000000000 : ℝ)=(50024610858685539057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34764412921452471/100000000000000000000 : ℝ) ≤ ((27300625498157386589/27310000000000000000 : ℝ)+2*(500381745189/273100000000000 : ℝ)*(14043/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (27300625498157386589/27310000000000000000 : ℝ)+2*(500381745189/273100000000000 : ℝ)*(14043/100000 : ℝ)=(10001713372337153/10000000000000000 : ℝ) by norm_num, show 1+2*(34764412921452471/100000000000000000000 : ℝ)=(50034764412921452471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27300625498157386589/27310000000000000000 : ℝ)*(X 1 0+X 2 0)+(500381745189/273100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27300625498157386589/27310000000000000000 : ℝ)) (alpha := (500381745189/273100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27300625498157386589/27310000000000000000 : ℝ)*(X 0 1+X 2 1)+(500381745189/273100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27300625498157386589/27310000000000000000 : ℝ)) (alpha := (500381745189/273100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27300625498157386589/27310000000000000000 : ℝ)*(X 0 2+X 1 2)+(500381745189/273100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27300625498157386589/27310000000000000000 : ℝ)) (alpha := (500381745189/273100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2178895363/10000000000 : ℝ)*X 0 0+(674190033/1250000000 : ℝ)*X 0 1+(5265291549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334053363/625000000 : ℝ)*X 1 0+(-448788421/2000000000 : ℝ)*X 1 1+(5265291551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344853809/10000000000 : ℝ)*X 2 0+(164540361/312500000 : ℝ)*X 2 1+(-2243942103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184102569/5000000000 : ℝ)*X 0 0+(4243122331/10000000000 : ℝ)*X 0 1+(1124244921/2500000000 : ℝ)*X 0 2+(2184102569/5000000000 : ℝ)*X 1 0+(4243122331/10000000000 : ℝ)*X 1 1+(1124244921/2500000000 : ℝ)*X 1 2+(2184102569/5000000000 : ℝ)*X 2 0+(4243122331/10000000000 : ℝ)*X 2 1+(1124244921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2178900311/10000000000 : ℝ)*X 0 0+(5265613541/10000000000 : ℝ)*X 0 1+(5393197111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312427277/10000000000 : ℝ)*X 1 0+(-2116036539/10000000000 : ℝ)*X 1 1+(674149639/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531242727/1000000000 : ℝ)*X 2 0+(674149639/1250000000 : ℝ)*X 2 1+(-529009137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136506717/312500000 : ℝ)*X 0 0+(899268449/2000000000 : ℝ)*X 0 1+(4243762069/10000000000 : ℝ)*X 0 2+(136506717/312500000 : ℝ)*X 1 0+(899268449/2000000000 : ℝ)*X 1 1+(4243762069/10000000000 : ℝ)*X 1 2+(136506717/312500000 : ℝ)*X 2 0+(899268449/2000000000 : ℝ)*X 2 1+(4243762069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6422762756382498126499001307/682750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374597137/20000000000000 : ℝ)*(base19) + (437308199/25000000000000 : ℝ)*(base23) + (66923977/100000000000000 : ℝ)*(lower2) + (235904709/100000000000000 : ℝ)*(upper3) + (18370207/12500000000000 : ℝ)*(upper5) + (5868971234341379/100000000000000 : ℝ)*(major0) + (5868971234341379/100000000000000 : ℝ)*(major1) + (5868971234341379/100000000000000 : ℝ)*(major2) + (7798618425378363/100000000000000 : ℝ)*(sp0) + (1559733512679783/20000000000000 : ℝ)*(sp1) + (1949666921787951/25000000000000 : ℝ)*(sp2) + (1969622564517737/50000000000000 : ℝ)*(sp3) + (51011006237/100000000000000 : ℝ)*(sp4) + (27589689489/100000000000000 : ℝ)*(sp7) + (984818179681241/25000000000000 : ℝ)*(f.failure) + (38993347181923/500000000000 : ℝ)*(f.sum) + (26696636951929/13655000000000000000000000000 : ℝ)*base66 + (58981509211077466231/2731000000000000000000000000000000 : ℝ)*base67 + (24478866856084466231/2731000000000000000000000000000000 : ℝ)*base69 + (2940287928522533769/2731000000000000000000000000000000 : ℝ)*base72 + (55686735374911/13655000000000000000000000000 : ℝ)*base73 + (91199022335683466231/2731000000000000000000000000000000 : ℝ)*base75 + (3314239761681466231/2731000000000000000000000000000000 : ℝ)*base77 + (9134049802248466231/2731000000000000000000000000000000 : ℝ)*base79 + (2137631373417/426718750000000000000000000 : ℝ)*base82 + (2493521/1250000000000000000000 : ℝ)*base89 + (2493521/1250000000000000000000 : ℝ)*base91 + (2493521/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1409524599450145406884392981/682750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15636219/4000000000000 : ℝ)*(base19) + (41689639/10000000000000 : ℝ)*(base23) + (45338729/100000000000000 : ℝ)*(upper3) + (8837331/50000000000000 : ℝ)*(lower4) + (10067849/25000000000000 : ℝ)*(upper5) + (5898568924780957/100000000000000 : ℝ)*(major0) + (5898568924780957/100000000000000 : ℝ)*(major1) + (5898568924780957/100000000000000 : ℝ)*(major2) + (10595905057/100000000000000 : ℝ)*(sp1) + (2773828729/25000000000000 : ℝ)*(sp2) + (3918999497619207/50000000000000 : ℝ)*(sp4) + (7837988008427881/100000000000000 : ℝ)*(sp5) + (1959496870756777/25000000000000 : ℝ)*(sp6) + (1979569392753723/50000000000000 : ℝ)*(sp7) + (1979569392753723/50000000000000 : ℝ)*(f.failure) + (3918999497619207/50000000000000 : ℝ)*(f.sum) + (29643383650977/13655000000000000000000000000 : ℝ)*base66 + (9672204428617685673/2731000000000000000000000000000000 : ℝ)*base67 + (19816319629813685673/2731000000000000000000000000000000 : ℝ)*base69 + (18121454505454685673/2731000000000000000000000000000000 : ℝ)*base71 + (38219558736157/13655000000000000000000000000 : ℝ)*base74 + (35796134927438685673/2731000000000000000000000000000000 : ℝ)*base75 + (2363593820686314327/2731000000000000000000000000000000 : ℝ)*base78 + (24430698422443685673/2731000000000000000000000000000000 : ℝ)*base79 + (85931335091363/13655000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24509437/2500000000000000000000 : ℝ)*base90 + (24509437/2500000000000000000000 : ℝ)*base92 + (24509437/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s8_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089452113/5000000000 : ℝ)*x 0 + (5393442103/10000000000 : ℝ)*x 1 + (1053072737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089452113/5000000000 : ℝ)^4155 ≤ (661877421531/5000000000000 : ℝ)^3131 := by
    have hnat : (1089452113 : ℕ)^4155*5000000000000^3131 ≤ 661877421531^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089452113 5000000000 661877421531 5000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393442103/10000000000 : ℝ)^4155 ≤ (22036481603241/50000000000000 : ℝ)^3131 := by
    have hnat : (5393442103 : ℕ)^4155*50000000000000^3131 ≤ 22036481603241^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393442103 10000000000 22036481603241 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053072737/2000000000 : ℝ)^4155 ≤ (42689488343371/100000000000000 : ℝ)^3131 := by
    have hnat : (1053072737 : ℕ)^4155*100000000000000^3131 ≤ 42689488343371^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053072737 2000000000 42689488343371 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089452113/5000000000 : ℝ), (5393442103/10000000000 : ℝ), (1053072737/2000000000 : ℝ)] ![(661877421531/5000000000000 : ℝ), (22036481603241/50000000000000 : ℝ), (42689488343371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089452113/5000000000 : ℝ)|^4155 ≤ (661877421531/5000000000000 : ℝ)^3131
        have hw : |(-1089452113/5000000000 : ℝ)|=(1089452113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393442103/10000000000 : ℝ)|^4155 ≤ (22036481603241/50000000000000 : ℝ)^3131
        have hw : |(5393442103/10000000000 : ℝ)|=(5393442103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053072737/2000000000 : ℝ)|^4155 ≤ (42689488343371/100000000000000 : ℝ)^3131
        have hw : |(1053072737/2000000000 : ℝ)|=(1053072737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336208401/2500000000 : ℝ)*x 0 + (-89754943/400000000 : ℝ)*x 1 + (658170463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336208401/2500000000 : ℝ)^4155 ≤ (21773312695997/50000000000000 : ℝ)^3131 := by
    have hnat : (1336208401 : ℕ)^4155*50000000000000^3131 ≤ 21773312695997^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336208401 2500000000 21773312695997 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89754943/400000000 : ℝ)^4155 ≤ (1720485757043/12500000000000 : ℝ)^3131 := by
    have hnat : (89754943 : ℕ)^4155*12500000000000^3131 ≤ 1720485757043^3131*400000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89754943 400000000 1720485757043 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658170463/1250000000 : ℝ)^4155 ≤ (10672372136949/25000000000000 : ℝ)^3131 := by
    have hnat : (658170463 : ℕ)^4155*25000000000000^3131 ≤ 10672372136949^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658170463 1250000000 10672372136949 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336208401/2500000000 : ℝ), (-89754943/400000000 : ℝ), (658170463/1250000000 : ℝ)] ![(21773312695997/50000000000000 : ℝ), (1720485757043/12500000000000 : ℝ), (10672372136949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336208401/2500000000 : ℝ)|^4155 ≤ (21773312695997/50000000000000 : ℝ)^3131
        have hw : |(1336208401/2500000000 : ℝ)|=(1336208401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89754943/400000000 : ℝ)|^4155 ≤ (1720485757043/12500000000000 : ℝ)^3131
        have hw : |(-89754943/400000000 : ℝ)|=(89754943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658170463/1250000000 : ℝ)|^4155 ≤ (10672372136949/25000000000000 : ℝ)^3131
        have hw : |(658170463/1250000000 : ℝ)|=(658170463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344833533/10000000000 : ℝ)*x 0 + (1053072751/2000000000 : ℝ)*x 1 + (-1402421/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344833533/10000000000 : ℝ)^4155 ≤ (21773312312169/50000000000000 : ℝ)^3131 := by
    have hnat : (5344833533 : ℕ)^4155*50000000000000^3131 ≤ 21773312312169^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344833533 10000000000 21773312312169 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053072751/2000000000 : ℝ)^4155 ≤ (10672372274129/25000000000000 : ℝ)^3131 := by
    have hnat : (1053072751 : ℕ)^4155*25000000000000^3131 ≤ 10672372274129^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053072751 2000000000 10672372274129 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1402421/6250000 : ℝ)^4155 ≤ (13763886259847/100000000000000 : ℝ)^3131 := by
    have hnat : (1402421 : ℕ)^4155*100000000000000^3131 ≤ 13763886259847^3131*6250000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402421 6250000 13763886259847 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344833533/10000000000 : ℝ), (1053072751/2000000000 : ℝ), (-1402421/6250000 : ℝ)] ![(21773312312169/50000000000000 : ℝ), (10672372274129/25000000000000 : ℝ), (13763886259847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344833533/10000000000 : ℝ)|^4155 ≤ (21773312312169/50000000000000 : ℝ)^3131
        have hw : |(5344833533/10000000000 : ℝ)|=(5344833533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053072751/2000000000 : ℝ)|^4155 ≤ (10672372274129/25000000000000 : ℝ)^3131
        have hw : |(1053072751/2000000000 : ℝ)|=(1053072751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1402421/6250000 : ℝ)|^4155 ≤ (13763886259847/100000000000000 : ℝ)^3131
        have hw : |(-1402421/6250000 : ℝ)|=(1402421/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184104483/5000000000 : ℝ)*x 0 + (1060817653/2500000000 : ℝ)*x 1 + (4496830401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184104483/5000000000 : ℝ)^4155 ≤ (33316846955403/100000000000000 : ℝ)^3131 := by
    have hnat : (2184104483 : ℕ)^4155*100000000000000^3131 ≤ 33316846955403^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184104483 5000000000 33316846955403 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060817653/2500000000 : ℝ)^4155 ≤ (32058225995557/100000000000000 : ℝ)^3131 := by
    have hnat : (1060817653 : ℕ)^4155*100000000000000^3131 ≤ 32058225995557^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060817653 2500000000 32058225995557 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496830401/10000000000 : ℝ)^4155 ≤ (34624927035379/100000000000000 : ℝ)^3131 := by
    have hnat : (4496830401 : ℕ)^4155*100000000000000^3131 ≤ 34624927035379^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496830401 10000000000 34624927035379 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184104483/5000000000 : ℝ), (1060817653/2500000000 : ℝ), (4496830401/10000000000 : ℝ)] ![(33316846955403/100000000000000 : ℝ), (32058225995557/100000000000000 : ℝ), (34624927035379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184104483/5000000000 : ℝ)|^4155 ≤ (33316846955403/100000000000000 : ℝ)^3131
        have hw : |(2184104483/5000000000 : ℝ)|=(2184104483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060817653/2500000000 : ℝ)|^4155 ≤ (32058225995557/100000000000000 : ℝ)^3131
        have hw : |(1060817653/2500000000 : ℝ)|=(1060817653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496830401/10000000000 : ℝ)|^4155 ≤ (34624927035379/100000000000000 : ℝ)^3131
        have hw : |(4496830401/10000000000 : ℝ)|=(4496830401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43578183/200000000 : ℝ)*x 0 + (2632842513/5000000000 : ℝ)*x 1 + (5393119611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43578183/200000000 : ℝ)^4155 ≤ (1654698516157/12500000000000 : ℝ)^3131 := by
    have hnat : (43578183 : ℕ)^4155*12500000000000^3131 ≤ 1654698516157^3131*200000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43578183 200000000 1654698516157 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632842513/5000000000 : ℝ)^4155 ≤ (8538589150877/20000000000000 : ℝ)^3131 := by
    have hnat : (2632842513 : ℕ)^4155*20000000000000^3131 ≤ 8538589150877^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632842513 5000000000 8538589150877 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393119611/10000000000 : ℝ)^4155 ≤ (11017366524933/25000000000000 : ℝ)^3131 := by
    have hnat : (5393119611 : ℕ)^4155*25000000000000^3131 ≤ 11017366524933^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393119611 10000000000 11017366524933 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43578183/200000000 : ℝ), (2632842513/5000000000 : ℝ), (5393119611/10000000000 : ℝ)] ![(1654698516157/12500000000000 : ℝ), (8538589150877/20000000000000 : ℝ), (11017366524933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43578183/200000000 : ℝ)|^4155 ≤ (1654698516157/12500000000000 : ℝ)^3131
        have hw : |(-43578183/200000000 : ℝ)|=(43578183/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632842513/5000000000 : ℝ)|^4155 ≤ (8538589150877/20000000000000 : ℝ)^3131
        have hw : |(2632842513/5000000000 : ℝ)|=(2632842513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393119611/10000000000 : ℝ)|^4155 ≤ (11017366524933/25000000000000 : ℝ)^3131
        have hw : |(5393119611/10000000000 : ℝ)|=(5393119611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312445087/10000000000 : ℝ)*x 0 + (-84644709/400000000 : ℝ)*x 1 + (5393119603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312445087/10000000000 : ℝ)^4155 ≤ (43196786424113/100000000000000 : ℝ)^3131 := by
    have hnat : (5312445087 : ℕ)^4155*100000000000000^3131 ≤ 43196786424113^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312445087 10000000000 43196786424113 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84644709/400000000 : ℝ)^4155 ≤ (3183436885013/25000000000000 : ℝ)^3131 := by
    have hnat : (84644709 : ℕ)^4155*25000000000000^3131 ≤ 3183436885013^3131*400000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84644709 400000000 3183436885013 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393119603/10000000000 : ℝ)^4155 ≤ (2203473300649/5000000000000 : ℝ)^3131 := by
    have hnat : (5393119603 : ℕ)^4155*5000000000000^3131 ≤ 2203473300649^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393119603 10000000000 2203473300649 5000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312445087/10000000000 : ℝ), (-84644709/400000000 : ℝ), (5393119603/10000000000 : ℝ)] ![(43196786424113/100000000000000 : ℝ), (3183436885013/25000000000000 : ℝ), (2203473300649/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312445087/10000000000 : ℝ)|^4155 ≤ (43196786424113/100000000000000 : ℝ)^3131
        have hw : |(5312445087/10000000000 : ℝ)|=(5312445087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84644709/400000000 : ℝ)|^4155 ≤ (3183436885013/25000000000000 : ℝ)^3131
        have hw : |(-84644709/400000000 : ℝ)|=(84644709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393119603/10000000000 : ℝ)|^4155 ≤ (2203473300649/5000000000000 : ℝ)^3131
        have hw : |(5393119603/10000000000 : ℝ)|=(5393119603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664055637/1250000000 : ℝ)*x 0 + (1348279899/2500000000 : ℝ)*x 1 + (-1058058861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664055637/1250000000 : ℝ)^4155 ≤ (10799196630307/25000000000000 : ℝ)^3131 := by
    have hnat : (664055637 : ℕ)^4155*25000000000000^3131 ≤ 10799196630307^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664055637 1250000000 10799196630307 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348279899/2500000000 : ℝ)^4155 ≤ (44069465937073/100000000000000 : ℝ)^3131 := by
    have hnat : (1348279899 : ℕ)^4155*100000000000000^3131 ≤ 44069465937073^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348279899 2500000000 44069465937073 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058058861/5000000000 : ℝ)^4155 ≤ (2546749503219/20000000000000 : ℝ)^3131 := by
    have hnat : (1058058861 : ℕ)^4155*20000000000000^3131 ≤ 2546749503219^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058058861 5000000000 2546749503219 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664055637/1250000000 : ℝ), (1348279899/2500000000 : ℝ), (-1058058861/5000000000 : ℝ)] ![(10799196630307/25000000000000 : ℝ), (44069465937073/100000000000000 : ℝ), (2546749503219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664055637/1250000000 : ℝ)|^4155 ≤ (10799196630307/25000000000000 : ℝ)^3131
        have hw : |(664055637/1250000000 : ℝ)|=(664055637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348279899/2500000000 : ℝ)|^4155 ≤ (44069465937073/100000000000000 : ℝ)^3131
        have hw : |(1348279899/2500000000 : ℝ)|=(1348279899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058058861/5000000000 : ℝ)|^4155 ≤ (2546749503219/20000000000000 : ℝ)^3131
        have hw : |(-1058058861/5000000000 : ℝ)|=(1058058861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s8_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4368218727/10000000000 : ℝ)*x 0 + (4496194253/10000000000 : ℝ)*x 1 + (2121954533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368218727/10000000000 : ℝ)^4155 ≤ (33316945752213/100000000000000 : ℝ)^3131 := by
    have hnat : (4368218727 : ℕ)^4155*100000000000000^3131 ≤ 33316945752213^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368218727 10000000000 33316945752213 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496194253/10000000000 : ℝ)^4155 ≤ (34618426959327/100000000000000 : ℝ)^3131 := by
    have hnat : (4496194253 : ℕ)^4155*100000000000000^3131 ≤ 34618426959327^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496194253 10000000000 34618426959327 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121954533/5000000000 : ℝ)^4155 ≤ (16032313639181/50000000000000 : ℝ)^3131 := by
    have hnat : (2121954533 : ℕ)^4155*50000000000000^3131 ≤ 16032313639181^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121954533 5000000000 16032313639181 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368218727/10000000000 : ℝ), (4496194253/10000000000 : ℝ), (2121954533/5000000000 : ℝ)] ![(33316945752213/100000000000000 : ℝ), (34618426959327/100000000000000 : ℝ), (16032313639181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368218727/10000000000 : ℝ)|^4155 ≤ (33316945752213/100000000000000 : ℝ)^3131
        have hw : |(4368218727/10000000000 : ℝ)|=(4368218727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496194253/10000000000 : ℝ)|^4155 ≤ (34618426959327/100000000000000 : ℝ)^3131
        have hw : |(4496194253/10000000000 : ℝ)|=(4496194253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121954533/5000000000 : ℝ)|^4155 ≤ (16032313639181/50000000000000 : ℝ)^3131
        have hw : |(2121954533/5000000000 : ℝ)|=(2121954533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11319/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (3623408824794771/25000000000000000000 : ℝ) := by
    have hpowers : (11319/100000 : ℝ)^8309 ≤ (3623408824794771/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11319 : ℕ)^8309*25000000000000000000^2048 ≤ 3623408824794771^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11319 100000 3623408824794771 25000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11319/100000 : ℝ)) (X := (3623408824794771/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/20000 : ℝ) ^ (8309/2048 : ℝ) ≤ (86710333118303/250000000000000000 : ℝ) := by
    have hpowers : (2807/20000 : ℝ)^8309 ≤ (86710333118303/250000000000000000 : ℝ)^2048 := by
      have hnat : (2807 : ℕ)^8309*250000000000000000^2048 ≤ 86710333118303^2048*20000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 20000 86710333118303 250000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/20000 : ℝ)) (X := (86710333118303/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503623408824794771/12500000000000000000 : ℝ) ≤ (1250089299927463/1250000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12503623408824794771/12500000000000000000 : ℝ)^2048 ≤ (1250089299927463/1250000000000000 : ℝ)^8309 := by
      have hnat : (12503623408824794771 : ℕ)^2048*1250000000000000^8309 ≤ 1250089299927463^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503623408824794771 12500000000000000000 1250089299927463 1250000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250089299927463/1250000000000000 : ℝ)) (X := (12503623408824794771/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012294442136625071/25000000000000000000 : ℝ) ≤ (5000605953871991/5000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (25012294442136625071/25000000000000000000 : ℝ)^2048 ≤ (5000605953871991/5000000000000000 : ℝ)^8309 := by
      have hnat : (25012294442136625071 : ℕ)^2048*5000000000000000^8309 ≤ 5000605953871991^8309*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012294442136625071 25000000000000000000 5000605953871991 5000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605953871991/5000000000000000 : ℝ)) (X := (25012294442136625071/25000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (125086710333118303/125000000000000000 : ℝ) ≤ (500085470803413/500000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (125086710333118303/125000000000000000 : ℝ)^2048 ≤ (500085470803413/500000000000000 : ℝ)^8309 := by
      have hnat : (125086710333118303 : ℕ)^2048*500000000000000^8309 ≤ 500085470803413^8309*125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125086710333118303 125000000000000000 500085470803413 500000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500085470803413/500000000000000 : ℝ)) (X := (125086710333118303/125000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3623408824794771/25000000000000000000 : ℝ) ≤ ((38786682450541301/38800000000000000 : ℝ)+2*(35536308877/19400000000000 : ℝ)*(11319/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (38786682450541301/38800000000000000 : ℝ)+2*(35536308877/19400000000000 : ℝ)*(11319/100000 : ℝ)=(1250089299927463/1250000000000000 : ℝ) by norm_num, show 1+2*(3623408824794771/25000000000000000000 : ℝ)=(12503623408824794771/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(86710333118303/250000000000000000 : ℝ)+(3623408824794771/25000000000000000000 : ℝ) ≤ ((38786682450541301/38800000000000000 : ℝ)+(35536308877/19400000000000 : ℝ)*((2807/20000 : ℝ)+(11319/100000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (38786682450541301/38800000000000000 : ℝ)+(35536308877/19400000000000 : ℝ)*((2807/20000 : ℝ)+(11319/100000 : ℝ))=(5000605953871991/5000000000000000 : ℝ) by norm_num, show 1+(86710333118303/250000000000000000 : ℝ)+(3623408824794771/25000000000000000000 : ℝ)=(25012294442136625071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(86710333118303/250000000000000000 : ℝ) ≤ ((38786682450541301/38800000000000000 : ℝ)+2*(35536308877/19400000000000 : ℝ)*(2807/20000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (38786682450541301/38800000000000000 : ℝ)+2*(35536308877/19400000000000 : ℝ)*(2807/20000 : ℝ)=(500085470803413/500000000000000 : ℝ) by norm_num, show 1+2*(86710333118303/250000000000000000 : ℝ)=(125086710333118303/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38786682450541301/38800000000000000 : ℝ)*(X 1 0+X 2 0)+(35536308877/19400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (38786682450541301/38800000000000000 : ℝ)) (alpha := (35536308877/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38786682450541301/38800000000000000 : ℝ)*(X 0 1+X 2 1)+(35536308877/19400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (38786682450541301/38800000000000000 : ℝ)) (alpha := (35536308877/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38786682450541301/38800000000000000 : ℝ)*(X 0 2+X 1 2)+(35536308877/19400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (38786682450541301/38800000000000000 : ℝ)) (alpha := (35536308877/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089452113/5000000000 : ℝ)*X 0 0+(5393442103/10000000000 : ℝ)*X 0 1+(1053072737/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336208401/2500000000 : ℝ)*X 1 0+(-89754943/400000000 : ℝ)*X 1 1+(658170463/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344833533/10000000000 : ℝ)*X 2 0+(1053072751/2000000000 : ℝ)*X 2 1+(-1402421/6250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184104483/5000000000 : ℝ)*X 0 0+(1060817653/2500000000 : ℝ)*X 0 1+(4496830401/10000000000 : ℝ)*X 0 2+(2184104483/5000000000 : ℝ)*X 1 0+(1060817653/2500000000 : ℝ)*X 1 1+(4496830401/10000000000 : ℝ)*X 1 2+(2184104483/5000000000 : ℝ)*X 2 0+(1060817653/2500000000 : ℝ)*X 2 1+(4496830401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43578183/200000000 : ℝ)*X 0 0+(2632842513/5000000000 : ℝ)*X 0 1+(5393119611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312445087/10000000000 : ℝ)*X 1 0+(-84644709/400000000 : ℝ)*X 1 1+(5393119603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664055637/1250000000 : ℝ)*X 2 0+(1348279899/2500000000 : ℝ)*X 2 1+(-1058058861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368218727/10000000000 : ℝ)*X 0 0+(4496194253/10000000000 : ℝ)*X 0 1+(2121954533/5000000000 : ℝ)*X 0 2+(4368218727/10000000000 : ℝ)*X 1 0+(4496194253/10000000000 : ℝ)*X 1 1+(2121954533/5000000000 : ℝ)*X 1 2+(4368218727/10000000000 : ℝ)*X 2 0+(4496194253/10000000000 : ℝ)*X 2 1+(2121954533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308717684067953093649/60625000000000000000000000 : ℝ) := by norm_num
    linear_combination (548115071/50000000000000 : ℝ)*(base19) + (923021949/100000000000000 : ℝ)*(base23) + (37141663/100000000000000 : ℝ)*(lower2) + (161656461/100000000000000 : ℝ)*(upper3) + (49553607/100000000000000 : ℝ)*(upper5) + (367239223086537/6250000000000 : ℝ)*(major0) + (367239223086537/6250000000000 : ℝ)*(major1) + (367239223086537/6250000000000 : ℝ)*(major2) + (7807751121814893/100000000000000 : ℝ)*(sp0) + (3903889579765317/50000000000000 : ℝ)*(sp1) + (3903889666369413/50000000000000 : ℝ)*(sp2) + (98596443921403/2500000000000 : ℝ)*(sp3) + (14566972941/50000000000000 : ℝ)*(sp4) + (84782053/500000000000 : ℝ)*(sp7) + (3943874713266721/100000000000000 : ℝ)*(f.failure) + (312311210230431/4000000000000 : ℝ)*(f.sum) + (853238305311/242500000000000000000000000 : ℝ)*base65 + (752527881845137/242500000000000000000000000000 : ℝ)*base67 + (547496715834863/242500000000000000000000000000 : ℝ)*base70 + (860519702382637/242500000000000000000000000000 : ℝ)*base71 + (910029213471/242500000000000000000000000 : ℝ)*base73 + (1764472230117363/242500000000000000000000000000 : ℝ)*base76 + (262702076797637/242500000000000000000000000000 : ℝ)*base77 + (2759174932512363/242500000000000000000000000000 : ℝ)*base80 + (399506303/7578125000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (22057401/5000000000000000000000 : ℝ)*base89 + (22057401/5000000000000000000000 : ℝ)*base91 + (22057401/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7889482554828958203440769/970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731934611/50000000000000 : ℝ)*(base19) + (1618217831/100000000000000 : ℝ)*(base23) + (64165373/12500000000000 : ℝ)*(lower1) + (38696587/25000000000000 : ℝ)*(upper3) + (64319467/100000000000000 : ℝ)*(lower4) + (165963161/100000000000000 : ℝ)*(upper5) + (5905434723586023/100000000000000 : ℝ)*(major0) + (5905434723586023/100000000000000 : ℝ)*(major1) + (5905434723586023/100000000000000 : ℝ)*(major2) + (1638696579/50000000000000 : ℝ)*(sp2) + (3923561021949307/50000000000000 : ℝ)*(sp4) + (490445036251837/6250000000000 : ℝ)*(sp5) + (980889643535953/12500000000000 : ℝ)*(sp6) + (1981873566078581/50000000000000 : ℝ)*(sp7) + (1981873566078581/50000000000000 : ℝ)*(f.failure) + (3923561021949307/50000000000000 : ℝ)*(f.sum) + (1291087007609/970000000000000000000000000 : ℝ)*base66 + (5728285714177923/3880000000000000000000000000000 : ℝ)*base67 + (17475689162302077/3880000000000000000000000000000 : ℝ)*base70 + (491416214886462077/3880000000000000000000000000000 : ℝ)*base72 + (60741743751/970000000000000000000000000 : ℝ)*base73 + (507334427783662077/3880000000000000000000000000000 : ℝ)*base76 + (28817247500782077/3880000000000000000000000000000 : ℝ)*base78 + (77516781498222077/3880000000000000000000000000000 : ℝ)*base80 + (3022042543091/970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11798061/2500000000000000000000 : ℝ)*base89 + (11798061/2500000000000000000000 : ℝ)*base91 + (11798061/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1117_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1117_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1117_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1117_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1117_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
