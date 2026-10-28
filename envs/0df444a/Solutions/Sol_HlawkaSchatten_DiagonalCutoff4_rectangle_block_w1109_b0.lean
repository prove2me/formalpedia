-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:12.063926+00:00
-- url     : https://prove2.me/submissions/b2902fc0-a1ad-458d-a583-dd229658c96f

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
theorem support_rectangle_w1109_s0_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23778741/125000000 : ℝ)*x 0 + (6061988777/10000000000 : ℝ)*x 1 + (2388142307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23778741/125000000 : ℝ)^4151 ≤ (1104749934509/10000000000000 : ℝ)^3127 := by
    have hnat : (23778741 : ℕ)^4151*10000000000000^3127 ≤ 1104749934509^3127*125000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23778741 125000000 1104749934509 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6061988777/10000000000 : ℝ)^4151 ≤ (51455050987513/100000000000000 : ℝ)^3127 := by
    have hnat : (6061988777 : ℕ)^4151*100000000000000^3127 ≤ 51455050987513^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6061988777 10000000000 51455050987513 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388142307/5000000000 : ℝ)^4151 ≤ (18748724831031/50000000000000 : ℝ)^3127 := by
    have hnat : (2388142307 : ℕ)^4151*50000000000000^3127 ≤ 18748724831031^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388142307 5000000000 18748724831031 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23778741/125000000 : ℝ), (6061988777/10000000000 : ℝ), (2388142307/5000000000 : ℝ)] ![(1104749934509/10000000000000 : ℝ), (51455050987513/100000000000000 : ℝ), (18748724831031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23778741/125000000 : ℝ)|^4151 ≤ (1104749934509/10000000000000 : ℝ)^3127
        have hw : |(-23778741/125000000 : ℝ)|=(23778741/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6061988777/10000000000 : ℝ)|^4151 ≤ (51455050987513/100000000000000 : ℝ)^3127
        have hw : |(6061988777/10000000000 : ℝ)|=(6061988777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388142307/5000000000 : ℝ)|^4151 ≤ (18748724831031/50000000000000 : ℝ)^3127
        have hw : |(2388142307/5000000000 : ℝ)|=(2388142307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5518652207/10000000000 : ℝ)*x 0 + (-660274517/2500000000 : ℝ)*x 1 + (4776284757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518652207/10000000000 : ℝ)^4151 ≤ (45424585982741/100000000000000 : ℝ)^3127 := by
    have hnat : (5518652207 : ℕ)^4151*100000000000000^3127 ≤ 45424585982741^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518652207 10000000000 45424585982741 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660274517/2500000000 : ℝ)^4151 ≤ (8538981425491/50000000000000 : ℝ)^3127 := by
    have hnat : (660274517 : ℕ)^4151*50000000000000^3127 ≤ 8538981425491^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660274517 2500000000 8538981425491 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776284757/10000000000 : ℝ)^4151 ≤ (18748725576179/50000000000000 : ℝ)^3127 := by
    have hnat : (4776284757 : ℕ)^4151*50000000000000^3127 ≤ 18748725576179^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776284757 10000000000 18748725576179 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518652207/10000000000 : ℝ), (-660274517/2500000000 : ℝ), (4776284757/10000000000 : ℝ)] ![(45424585982741/100000000000000 : ℝ), (8538981425491/50000000000000 : ℝ), (18748725576179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518652207/10000000000 : ℝ)|^4151 ≤ (45424585982741/100000000000000 : ℝ)^3127
        have hw : |(5518652207/10000000000 : ℝ)|=(5518652207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660274517/2500000000 : ℝ)|^4151 ≤ (8538981425491/50000000000000 : ℝ)^3127
        have hw : |(-660274517/2500000000 : ℝ)|=(660274517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4776284757/10000000000 : ℝ)|^4151 ≤ (18748725576179/50000000000000 : ℝ)^3127
        have hw : |(4776284757/10000000000 : ℝ)|=(4776284757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (689831561/1250000000 : ℝ)*x 0 + (238814223/500000000 : ℝ)*x 1 + (-264109807/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689831561/1250000000 : ℝ)^4151 ≤ (454245890531/1000000000000 : ℝ)^3127 := by
    have hnat : (689831561 : ℕ)^4151*1000000000000^3127 ≤ 454245890531^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689831561 1250000000 454245890531 1000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238814223/500000000 : ℝ)^4151 ≤ (4687181007141/12500000000000 : ℝ)^3127 := by
    have hnat : (238814223 : ℕ)^4151*12500000000000^3127 ≤ 4687181007141^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238814223 500000000 4687181007141 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264109807/1000000000 : ℝ)^4151 ≤ (341559257363/2000000000000 : ℝ)^3127 := by
    have hnat : (264109807 : ℕ)^4151*2000000000000^3127 ≤ 341559257363^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264109807 1000000000 341559257363 2000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689831561/1250000000 : ℝ), (238814223/500000000 : ℝ), (-264109807/1000000000 : ℝ)] ![(454245890531/1000000000000 : ℝ), (4687181007141/12500000000000 : ℝ), (341559257363/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689831561/1250000000 : ℝ)|^4151 ≤ (454245890531/1000000000000 : ℝ)^3127
        have hw : |(689831561/1250000000 : ℝ)|=(689831561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238814223/500000000 : ℝ)|^4151 ≤ (4687181007141/12500000000000 : ℝ)^3127
        have hw : |(238814223/500000000 : ℝ)|=(238814223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264109807/1000000000 : ℝ)|^4151 ≤ (341559257363/2000000000000 : ℝ)^3127
        have hw : |(-264109807/1000000000 : ℝ)|=(264109807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203673281/10000000000 : ℝ)*x 0 + (3122657071/10000000000 : ℝ)*x 1 + (2831993291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203673281/10000000000 : ℝ)^4151 ≤ (6330070777797/20000000000000 : ℝ)^3127 := by
    have hnat : (4203673281 : ℕ)^4151*20000000000000^3127 ≤ 6330070777797^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203673281 10000000000 6330070777797 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122657071/10000000000 : ℝ)^4151 ≤ (21330250274759/100000000000000 : ℝ)^3127 := by
    have hnat : (3122657071 : ℕ)^4151*100000000000000^3127 ≤ 21330250274759^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122657071 10000000000 21330250274759 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831993291/5000000000 : ℝ)^4151 ≤ (47019395832479/100000000000000 : ℝ)^3127 := by
    have hnat : (2831993291 : ℕ)^4151*100000000000000^3127 ≤ 47019395832479^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831993291 5000000000 47019395832479 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203673281/10000000000 : ℝ), (3122657071/10000000000 : ℝ), (2831993291/5000000000 : ℝ)] ![(6330070777797/20000000000000 : ℝ), (21330250274759/100000000000000 : ℝ), (47019395832479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203673281/10000000000 : ℝ)|^4151 ≤ (6330070777797/20000000000000 : ℝ)^3127
        have hw : |(4203673281/10000000000 : ℝ)|=(4203673281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122657071/10000000000 : ℝ)|^4151 ≤ (21330250274759/100000000000000 : ℝ)^3127
        have hw : |(3122657071/10000000000 : ℝ)|=(3122657071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831993291/5000000000 : ℝ)|^4151 ≤ (47019395832479/100000000000000 : ℝ)^3127
        have hw : |(2831993291/5000000000 : ℝ)|=(2831993291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-953771871/5000000000 : ℝ)*x 0 + (2404733823/5000000000 : ℝ)*x 1 + (6027640961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953771871/5000000000 : ℝ)^4151 ≤ (11087948254127/100000000000000 : ℝ)^3127 := by
    have hnat : (953771871 : ℕ)^4151*100000000000000^3127 ≤ 11087948254127^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953771871 5000000000 11087948254127 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404733823/5000000000 : ℝ)^4151 ≤ (37843664305197/100000000000000 : ℝ)^3127 := by
    have hnat : (2404733823 : ℕ)^4151*100000000000000^3127 ≤ 37843664305197^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404733823 5000000000 37843664305197 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6027640961/10000000000 : ℝ)^4151 ≤ (51068387421337/100000000000000 : ℝ)^3127 := by
    have hnat : (6027640961 : ℕ)^4151*100000000000000^3127 ≤ 51068387421337^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6027640961 10000000000 51068387421337 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953771871/5000000000 : ℝ), (2404733823/5000000000 : ℝ), (6027640961/10000000000 : ℝ)] ![(11087948254127/100000000000000 : ℝ), (37843664305197/100000000000000 : ℝ), (51068387421337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953771871/5000000000 : ℝ)|^4151 ≤ (11087948254127/100000000000000 : ℝ)^3127
        have hw : |(-953771871/5000000000 : ℝ)|=(953771871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404733823/5000000000 : ℝ)|^4151 ≤ (37843664305197/100000000000000 : ℝ)^3127
        have hw : |(2404733823/5000000000 : ℝ)|=(2404733823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6027640961/10000000000 : ℝ)|^4151 ≤ (51068387421337/100000000000000 : ℝ)^3127
        have hw : |(6027640961/10000000000 : ℝ)|=(6027640961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033892497/2000000000 : ℝ)*x 0 + (-138974269/1000000000 : ℝ)*x 1 + (1506910717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033892497/2000000000 : ℝ)^4151 ≤ (20824627104671/50000000000000 : ℝ)^3127 := by
    have hnat : (1033892497 : ℕ)^4151*50000000000000^3127 ≤ 20824627104671^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033892497 2000000000 20824627104671 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138974269/1000000000 : ℝ)^4151 ≤ (910292112607/12500000000000 : ℝ)^3127 := by
    have hnat : (138974269 : ℕ)^4151*12500000000000^3127 ≤ 910292112607^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138974269 1000000000 910292112607 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506910717/2500000000 : ℝ)^4151 ≤ (25534204434509/50000000000000 : ℝ)^3127 := by
    have hnat : (1506910717 : ℕ)^4151*50000000000000^3127 ≤ 25534204434509^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506910717 2500000000 25534204434509 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033892497/2000000000 : ℝ), (-138974269/1000000000 : ℝ), (1506910717/2500000000 : ℝ)] ![(20824627104671/50000000000000 : ℝ), (910292112607/12500000000000 : ℝ), (25534204434509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033892497/2000000000 : ℝ)|^4151 ≤ (20824627104671/50000000000000 : ℝ)^3127
        have hw : |(1033892497/2000000000 : ℝ)|=(1033892497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138974269/1000000000 : ℝ)|^4151 ≤ (910292112607/12500000000000 : ℝ)^3127
        have hw : |(-138974269/1000000000 : ℝ)|=(138974269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506910717/2500000000 : ℝ)|^4151 ≤ (25534204434509/50000000000000 : ℝ)^3127
        have hw : |(1506910717/2500000000 : ℝ)|=(1506910717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (161545783/312500000 : ℝ)*x 0 + (6027641469/10000000000 : ℝ)*x 1 + (-1389741/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161545783/312500000 : ℝ)^4151 ≤ (41649281706563/100000000000000 : ℝ)^3127 := by
    have hnat : (161545783 : ℕ)^4151*100000000000000^3127 ≤ 41649281706563^3127*312500000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161545783 312500000 41649281706563 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6027641469/10000000000 : ℝ)^4151 ≤ (79794364273/156250000000 : ℝ)^3127 := by
    have hnat : (6027641469 : ℕ)^4151*156250000000^3127 ≤ 79794364273^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6027641469 10000000000 79794364273 156250000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389741/10000000 : ℝ)^4151 ≤ (7282325145173/100000000000000 : ℝ)^3127 := by
    have hnat : (1389741 : ℕ)^4151*100000000000000^3127 ≤ 7282325145173^3127*10000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389741 10000000 7282325145173 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161545783/312500000 : ℝ), (6027641469/10000000000 : ℝ), (-1389741/10000000 : ℝ)] ![(41649281706563/100000000000000 : ℝ), (79794364273/156250000000 : ℝ), (7282325145173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161545783/312500000 : ℝ)|^4151 ≤ (41649281706563/100000000000000 : ℝ)^3127
        have hw : |(161545783/312500000 : ℝ)|=(161545783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6027641469/10000000000 : ℝ)|^4151 ≤ (79794364273/156250000000 : ℝ)^3127
        have hw : |(6027641469/10000000000 : ℝ)|=(6027641469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389741/10000000 : ℝ)|^4151 ≤ (7282325145173/100000000000000 : ℝ)^3127
        have hw : |(-1389741/10000000 : ℝ)|=(1389741/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s0_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214036189/10000000000 : ℝ)*x 0 + (174949969/312500000 : ℝ)*x 1 + (49852289/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214036189/10000000000 : ℝ)^4151 ≤ (31753970951819/100000000000000 : ℝ)^3127 := by
    have hnat : (4214036189 : ℕ)^4151*100000000000000^3127 ≤ 31753970951819^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214036189 10000000000 31753970951819 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174949969/312500000 : ℝ)^4151 ≤ (46297997911999/100000000000000 : ℝ)^3127 := by
    have hnat : (174949969 : ℕ)^4151*100000000000000^3127 ≤ 46297997911999^3127*312500000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174949969 312500000 46297997911999 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49852289/156250000 : ℝ)^4151 ≤ (5487007779221/25000000000000 : ℝ)^3127 := by
    have hnat : (49852289 : ℕ)^4151*25000000000000^3127 ≤ 5487007779221^3127*156250000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49852289 156250000 5487007779221 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214036189/10000000000 : ℝ), (174949969/312500000 : ℝ), (49852289/156250000 : ℝ)] ![(31753970951819/100000000000000 : ℝ), (46297997911999/100000000000000 : ℝ), (5487007779221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214036189/10000000000 : ℝ)|^4151 ≤ (31753970951819/100000000000000 : ℝ)^3127
        have hw : |(4214036189/10000000000 : ℝ)|=(4214036189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174949969/312500000 : ℝ)|^4151 ≤ (46297997911999/100000000000000 : ℝ)^3127
        have hw : |(174949969/312500000 : ℝ)|=(174949969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49852289/156250000 : ℝ)|^4151 ≤ (5487007779221/25000000000000 : ℝ)^3127
        have hw : |(49852289/156250000 : ℝ)|=(49852289/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13971/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8301/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8301 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8301*1^2048 ≤ 0^2048*1^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8301/2048 : ℝ) ≤ (1219075337484595613/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8301 ≤ (1219075337484595613/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8301*50000000000000000000^2048 ≤ 1219075337484595613^2048*5^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1219075337484595613 50000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1219075337484595613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8301 := by
      have hnat : (1 : ℕ)^2048*1^8301 ≤ 1^8301*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51219075337484595613/50000000000000000000 : ℝ) ≤ (628725545873781/625000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (51219075337484595613/50000000000000000000 : ℝ)^2048 ≤ (628725545873781/625000000000000 : ℝ)^8301 := by
      have hnat : (51219075337484595613 : ℕ)^2048*625000000000000^8301 ≤ 628725545873781^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51219075337484595613 50000000000000000000 628725545873781 625000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628725545873781/625000000000000 : ℝ)) (X := (51219075337484595613/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26219075337484595613/25000000000000000000 : ℝ) ≤ (316225545873781/312500000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (26219075337484595613/25000000000000000000 : ℝ)^2048 ≤ (316225545873781/312500000000000 : ℝ)^8301 := by
      have hnat : (26219075337484595613 : ℕ)^2048*312500000000000^8301 ≤ 316225545873781^8301*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26219075337484595613 25000000000000000000 316225545873781 312500000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (316225545873781/312500000000000 : ℝ)) (X := (26219075337484595613/25000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3725545873781/250000000000000 : ℝ)*(0 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3725545873781/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1219075337484595613/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3725545873781/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (1 : ℝ)+(3725545873781/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628725545873781/625000000000000 : ℝ) by norm_num, show 1+(1219075337484595613/50000000000000000000 : ℝ)+(0 : ℝ)=(51219075337484595613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1219075337484595613/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3725545873781/250000000000000 : ℝ)*(2/5 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3725545873781/250000000000000 : ℝ)*(2/5 : ℝ)=(316225545873781/312500000000000 : ℝ) by norm_num, show 1+2*(1219075337484595613/50000000000000000000 : ℝ)=(26219075337484595613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3725545873781/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3725545873781/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3725545873781/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3725545873781/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3725545873781/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3725545873781/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23778741/125000000 : ℝ)*X 0 0+(6061988777/10000000000 : ℝ)*X 0 1+(2388142307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518652207/10000000000 : ℝ)*X 1 0+(-660274517/2500000000 : ℝ)*X 1 1+(4776284757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689831561/1250000000 : ℝ)*X 2 0+(238814223/500000000 : ℝ)*X 2 1+(-264109807/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203673281/10000000000 : ℝ)*X 0 0+(3122657071/10000000000 : ℝ)*X 0 1+(2831993291/5000000000 : ℝ)*X 0 2+(4203673281/10000000000 : ℝ)*X 1 0+(3122657071/10000000000 : ℝ)*X 1 1+(2831993291/5000000000 : ℝ)*X 1 2+(4203673281/10000000000 : ℝ)*X 2 0+(3122657071/10000000000 : ℝ)*X 2 1+(2831993291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-953771871/5000000000 : ℝ)*X 0 0+(2404733823/5000000000 : ℝ)*X 0 1+(6027640961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1033892497/2000000000 : ℝ)*X 1 0+(-138974269/1000000000 : ℝ)*X 1 1+(1506910717/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161545783/312500000 : ℝ)*X 2 0+(6027641469/10000000000 : ℝ)*X 2 1+(-1389741/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214036189/10000000000 : ℝ)*X 0 0+(174949969/312500000 : ℝ)*X 0 1+(49852289/156250000 : ℝ)*X 0 2+(4214036189/10000000000 : ℝ)*X 1 0+(174949969/312500000 : ℝ)*X 1 1+(49852289/156250000 : ℝ)*X 1 2+(4214036189/10000000000 : ℝ)*X 2 0+(174949969/312500000 : ℝ)*X 2 1+(49852289/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45947944928678313/12500000000000000000000 : ℝ) := by norm_num
    linear_combination (39050347/100000000000000 : ℝ)*(base1) + (226427851/25000000000000 : ℝ)*(base19) + (876071331/100000000000000 : ℝ)*(base23) + (69243657/100000000000000 : ℝ)*(base24) + (217659489/100000000000000 : ℝ)*(upper3) + (585643208299953/100000000000000 : ℝ)*(major0) + (585643208299953/100000000000000 : ℝ)*(major1) + (585643208299953/100000000000000 : ℝ)*(major2) + (97223364281427/12500000000000 : ℝ)*(sp0) + (777787950773269/100000000000000 : ℝ)*(sp1) + (388893955584843/50000000000000 : ℝ)*(sp2) + (98373938525737/25000000000000 : ℝ)*(sp3) + (1981283603/100000000000000 : ℝ)*(sp4) + (65777363/4000000000000 : ℝ)*(sp7) + (393497437587369/100000000000000 : ℝ)*(f.failure) + (777788856484673/100000000000000 : ℝ)*(f.sum) + (26909444480207/12500000000000000000000000000 : ℝ)*base66 + (72523184282293/25000000000000000000000000000 : ℝ)*base67 + (227044155157293/25000000000000000000000000000 : ℝ)*base69 + (20862745082293/25000000000000000000000000000 : ℝ)*base71 + (20579056467707/12500000000000000000000000000 : ℝ)*base74 + (109074537007293/25000000000000000000000000000 : ℝ)*base75 + (36902857042707/25000000000000000000000000000 : ℝ)*base78 + (185919635467707/25000000000000000000000000000 : ℝ)*base80 + (60643564782293/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (87649857/10000000000000000000000 : ℝ)*base90 + (87649857/10000000000000000000000 : ℝ)*base92 + (87649857/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12925940519691089884053/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170349663/100000000000000 : ℝ)*(base19) + (572730737/50000000000000 : ℝ)*(base23) + (543528333/100000000000000 : ℝ)*(base39) + (66389281/50000000000000 : ℝ)*(base45) + (22858881/25000000000000 : ℝ)*(upper3) + (131358097/50000000000000 : ℝ)*(upper5) + (61810252051561/10000000000000 : ℝ)*(major0) + (61810252051561/10000000000000 : ℝ)*(major1) + (618101976987277/100000000000000 : ℝ)*(major2) + (18035333/3125000000000 : ℝ)*(sp2) + (205224325358541/25000000000000 : ℝ)*(sp4) + (820897131084501/100000000000000 : ℝ)*(sp5) + (12826501912037/1562500000000 : ℝ)*(sp6) + (25956691137001/6250000000000 : ℝ)*(sp7) + (25956691137001/6250000000000 : ℝ)*(f.failure) + (820897844962497/100000000000000 : ℝ)*(f.sum) + (34110648294253/25000000000000000000000000000 : ℝ)*base66 + (316679566915663/25000000000000000000000000000 : ℝ)*base68 + (17614308827859/2500000000000000000000000000 : ℝ)*base70 + (162037915340663/25000000000000000000000000000 : ℝ)*base72 + (195090825844253/25000000000000000000000000000 : ℝ)*base74 + (918698012141/2500000000000000000000000000 : ℝ)*base75 + (23916889377859/2500000000000000000000000000 : ℝ)*base78 + (35886181177859/2500000000000000000000000000 : ℝ)*base80 + (138707497859/1250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7169247/625000000000000000000 : ℝ)*base89 + (7169247/625000000000000000000 : ℝ)*base91 + (7169247/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1109_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13971/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s1_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109345911/10000000000 : ℝ)*x 0 + (142760453/250000000 : ℝ)*x 1 + (249764449/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109345911/10000000000 : ℝ)^4151 ≤ (12671446786147/100000000000000 : ℝ)^3127 := by
    have hnat : (2109345911 : ℕ)^4151*100000000000000^3127 ≤ 12671446786147^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109345911 10000000000 12671446786147 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142760453/250000000 : ℝ)^4151 ≤ (47531754661359/100000000000000 : ℝ)^3127 := by
    have hnat : (142760453 : ℕ)^4151*100000000000000^3127 ≤ 47531754661359^3127*250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142760453 250000000 47531754661359 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249764449/500000000 : ℝ)^4151 ≤ (9949199634287/25000000000000 : ℝ)^3127 := by
    have hnat : (249764449 : ℕ)^4151*25000000000000^3127 ≤ 9949199634287^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249764449 500000000 9949199634287 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109345911/10000000000 : ℝ), (142760453/250000000 : ℝ), (249764449/500000000 : ℝ)] ![(12671446786147/100000000000000 : ℝ), (47531754661359/100000000000000 : ℝ), (9949199634287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109345911/10000000000 : ℝ)|^4151 ≤ (12671446786147/100000000000000 : ℝ)^3127
        have hw : |(-2109345911/10000000000 : ℝ)|=(2109345911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142760453/250000000 : ℝ)|^4151 ≤ (47531754661359/100000000000000 : ℝ)^3127
        have hw : |(142760453/250000000 : ℝ)|=(142760453/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249764449/500000000 : ℝ)|^4151 ≤ (9949199634287/25000000000000 : ℝ)^3127
        have hw : |(249764449/500000000 : ℝ)|=(249764449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420937719/10000000000 : ℝ)*x 0 + (-499184937/2000000000 : ℝ)*x 1 + (1248822243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420937719/10000000000 : ℝ)^4151 ≤ (44360012093557/100000000000000 : ℝ)^3127 := by
    have hnat : (5420937719 : ℕ)^4151*100000000000000^3127 ≤ 44360012093557^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420937719 10000000000 44360012093557 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499184937/2000000000 : ℝ)^4151 ≤ (3960797361199/25000000000000 : ℝ)^3127 := by
    have hnat : (499184937 : ℕ)^4151*25000000000000^3127 ≤ 3960797361199^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499184937 2000000000 3960797361199 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248822243/2500000000 : ℝ)^4151 ≤ (19898399226271/50000000000000 : ℝ)^3127 := by
    have hnat : (1248822243 : ℕ)^4151*50000000000000^3127 ≤ 19898399226271^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248822243 2500000000 19898399226271 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420937719/10000000000 : ℝ), (-499184937/2000000000 : ℝ), (1248822243/2500000000 : ℝ)] ![(44360012093557/100000000000000 : ℝ), (3960797361199/25000000000000 : ℝ), (19898399226271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420937719/10000000000 : ℝ)|^4151 ≤ (44360012093557/100000000000000 : ℝ)^3127
        have hw : |(5420937719/10000000000 : ℝ)|=(5420937719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499184937/2000000000 : ℝ)|^4151 ≤ (3960797361199/25000000000000 : ℝ)^3127
        have hw : |(-499184937/2000000000 : ℝ)|=(499184937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248822243/2500000000 : ℝ)|^4151 ≤ (19898399226271/50000000000000 : ℝ)^3127
        have hw : |(1248822243/2500000000 : ℝ)|=(1248822243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420938981/10000000000 : ℝ)*x 0 + (499528777/1000000000 : ℝ)*x 1 + (-499184913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420938981/10000000000 : ℝ)^4151 ≤ (44360025802421/100000000000000 : ℝ)^3127 := by
    have hnat : (5420938981 : ℕ)^4151*100000000000000^3127 ≤ 44360025802421^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420938981 10000000000 44360025802421 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499528777/1000000000 : ℝ)^4151 ≤ (4974598217557/12500000000000 : ℝ)^3127 := by
    have hnat : (499528777 : ℕ)^4151*12500000000000^3127 ≤ 4974598217557^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499528777 1000000000 4974598217557 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499184913/2000000000 : ℝ)^4151 ≤ (7921594216821/50000000000000 : ℝ)^3127 := by
    have hnat : (499184913 : ℕ)^4151*50000000000000^3127 ≤ 7921594216821^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499184913 2000000000 7921594216821 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420938981/10000000000 : ℝ), (499528777/1000000000 : ℝ), (-499184913/2000000000 : ℝ)] ![(44360025802421/100000000000000 : ℝ), (4974598217557/12500000000000 : ℝ), (7921594216821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420938981/10000000000 : ℝ)|^4151 ≤ (44360025802421/100000000000000 : ℝ)^3127
        have hw : |(5420938981/10000000000 : ℝ)|=(5420938981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499528777/1000000000 : ℝ)|^4151 ≤ (4974598217557/12500000000000 : ℝ)^3127
        have hw : |(499528777/1000000000 : ℝ)|=(499528777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499184913/2000000000 : ℝ)|^4151 ≤ (7921594216821/50000000000000 : ℝ)^3127
        have hw : |(-499184913/2000000000 : ℝ)|=(499184913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320220661/10000000000 : ℝ)*x 0 + (458850597/1250000000 : ℝ)*x 1 + (2542165481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320220661/10000000000 : ℝ)^4151 ≤ (16410239065641/50000000000000 : ℝ)^3127 := by
    have hnat : (4320220661 : ℕ)^4151*50000000000000^3127 ≤ 16410239065641^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320220661 10000000000 16410239065641 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458850597/1250000000 : ℝ)^4151 ≤ (26438297471479/100000000000000 : ℝ)^3127 := by
    have hnat : (458850597 : ℕ)^4151*100000000000000^3127 ≤ 26438297471479^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458850597 1250000000 26438297471479 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542165481/5000000000 : ℝ)^4151 ≤ (40741224390759/100000000000000 : ℝ)^3127 := by
    have hnat : (2542165481 : ℕ)^4151*100000000000000^3127 ≤ 40741224390759^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542165481 5000000000 40741224390759 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320220661/10000000000 : ℝ), (458850597/1250000000 : ℝ), (2542165481/5000000000 : ℝ)] ![(16410239065641/50000000000000 : ℝ), (26438297471479/100000000000000 : ℝ), (40741224390759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320220661/10000000000 : ℝ)|^4151 ≤ (16410239065641/50000000000000 : ℝ)^3127
        have hw : |(4320220661/10000000000 : ℝ)|=(4320220661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458850597/1250000000 : ℝ)|^4151 ≤ (26438297471479/100000000000000 : ℝ)^3127
        have hw : |(458850597/1250000000 : ℝ)|=(458850597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542165481/5000000000 : ℝ)|^4151 ≤ (40741224390759/100000000000000 : ℝ)^3127
        have hw : |(2542165481/5000000000 : ℝ)|=(2542165481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527549803/2500000000 : ℝ)*x 0 + (5005177199/10000000000 : ℝ)*x 1 + (2850165967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527549803/2500000000 : ℝ)^4151 ≤ (12678251882331/100000000000000 : ℝ)^3127 := by
    have hnat : (527549803 : ℕ)^4151*100000000000000^3127 ≤ 12678251882331^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527549803 2500000000 12678251882331 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005177199/10000000000 : ℝ)^4151 ≤ (39901408036581/100000000000000 : ℝ)^3127 := by
    have hnat : (5005177199 : ℕ)^4151*100000000000000^3127 ≤ 39901408036581^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005177199 10000000000 39901408036581 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850165967/5000000000 : ℝ)^4151 ≤ (23710170031853/50000000000000 : ℝ)^3127 := by
    have hnat : (2850165967 : ℕ)^4151*50000000000000^3127 ≤ 23710170031853^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850165967 5000000000 23710170031853 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527549803/2500000000 : ℝ), (5005177199/10000000000 : ℝ), (2850165967/5000000000 : ℝ)] ![(12678251882331/100000000000000 : ℝ), (39901408036581/100000000000000 : ℝ), (23710170031853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527549803/2500000000 : ℝ)|^4151 ≤ (12678251882331/100000000000000 : ℝ)^3127
        have hw : |(-527549803/2500000000 : ℝ)|=(527549803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005177199/10000000000 : ℝ)|^4151 ≤ (39901408036581/100000000000000 : ℝ)^3127
        have hw : |(5005177199/10000000000 : ℝ)|=(5005177199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850165967/5000000000 : ℝ)|^4151 ≤ (23710170031853/50000000000000 : ℝ)^3127
        have hw : |(2850165967/5000000000 : ℝ)|=(2850165967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1309474383/2500000000 : ℝ)*x 0 + (-895440687/5000000000 : ℝ)*x 1 + (2850165871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309474383/2500000000 : ℝ)^4151 ≤ (21191379403451/50000000000000 : ℝ)^3127 := by
    have hnat : (1309474383 : ℕ)^4151*50000000000000^3127 ≤ 21191379403451^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309474383 2500000000 21191379403451 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895440687/5000000000 : ℝ)^4151 ≤ (2549225809337/25000000000000 : ℝ)^3127 := by
    have hnat : (895440687 : ℕ)^4151*25000000000000^3127 ≤ 2549225809337^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895440687 5000000000 2549225809337 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850165871/5000000000 : ℝ)^4151 ≤ (47420337943439/100000000000000 : ℝ)^3127 := by
    have hnat : (2850165871 : ℕ)^4151*100000000000000^3127 ≤ 47420337943439^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850165871 5000000000 47420337943439 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309474383/2500000000 : ℝ), (-895440687/5000000000 : ℝ), (2850165871/5000000000 : ℝ)] ![(21191379403451/50000000000000 : ℝ), (2549225809337/25000000000000 : ℝ), (47420337943439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309474383/2500000000 : ℝ)|^4151 ≤ (21191379403451/50000000000000 : ℝ)^3127
        have hw : |(1309474383/2500000000 : ℝ)|=(1309474383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-895440687/5000000000 : ℝ)|^4151 ≤ (2549225809337/25000000000000 : ℝ)^3127
        have hw : |(-895440687/5000000000 : ℝ)|=(895440687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850165871/5000000000 : ℝ)|^4151 ≤ (47420337943439/100000000000000 : ℝ)^3127
        have hw : |(2850165871/5000000000 : ℝ)|=(2850165871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2618948779/5000000000 : ℝ)*x 0 + (2850165941/5000000000 : ℝ)*x 1 + (-1790881131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618948779/5000000000 : ℝ)^4151 ≤ (1324461221443/3125000000000 : ℝ)^3127 := by
    have hnat : (2618948779 : ℕ)^4151*3125000000000^3127 ≤ 1324461221443^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618948779 5000000000 1324461221443 3125000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850165941/5000000000 : ℝ)^4151 ≤ (47420339489467/100000000000000 : ℝ)^3127 := by
    have hnat : (2850165941 : ℕ)^4151*100000000000000^3127 ≤ 47420339489467^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850165941 5000000000 47420339489467 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790881131/10000000000 : ℝ)^4151 ≤ (318653168771/3125000000000 : ℝ)^3127 := by
    have hnat : (1790881131 : ℕ)^4151*3125000000000^3127 ≤ 318653168771^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790881131 10000000000 318653168771 3125000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618948779/5000000000 : ℝ), (2850165941/5000000000 : ℝ), (-1790881131/10000000000 : ℝ)] ![(1324461221443/3125000000000 : ℝ), (47420339489467/100000000000000 : ℝ), (318653168771/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618948779/5000000000 : ℝ)|^4151 ≤ (1324461221443/3125000000000 : ℝ)^3127
        have hw : |(2618948779/5000000000 : ℝ)|=(2618948779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850165941/5000000000 : ℝ)|^4151 ≤ (47420339489467/100000000000000 : ℝ)^3127
        have hw : |(2850165941/5000000000 : ℝ)|=(2850165941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790881131/10000000000 : ℝ)|^4151 ≤ (318653168771/3125000000000 : ℝ)^3127
        have hw : |(-1790881131/10000000000 : ℝ)|=(1790881131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s1_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160952881/5000000000 : ℝ)*x 0 + (1266196649/2500000000 : ℝ)*x 1 + (1845370169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160952881/5000000000 : ℝ)^4151 ≤ (32837472987527/100000000000000 : ℝ)^3127 := by
    have hnat : (2160952881 : ℕ)^4151*100000000000000^3127 ≤ 32837472987527^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160952881 5000000000 32837472987527 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266196649/2500000000 : ℝ)^4151 ≤ (40533459082029/100000000000000 : ℝ)^3127 := by
    have hnat : (1266196649 : ℕ)^4151*100000000000000^3127 ≤ 40533459082029^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266196649 2500000000 40533459082029 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845370169/5000000000 : ℝ)^4151 ≤ (26629067908767/100000000000000 : ℝ)^3127 := by
    have hnat : (1845370169 : ℕ)^4151*100000000000000^3127 ≤ 26629067908767^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845370169 5000000000 26629067908767 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160952881/5000000000 : ℝ), (1266196649/2500000000 : ℝ), (1845370169/5000000000 : ℝ)] ![(32837472987527/100000000000000 : ℝ), (40533459082029/100000000000000 : ℝ), (26629067908767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160952881/5000000000 : ℝ)|^4151 ≤ (32837472987527/100000000000000 : ℝ)^3127
        have hw : |(2160952881/5000000000 : ℝ)|=(2160952881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266196649/2500000000 : ℝ)|^4151 ≤ (40533459082029/100000000000000 : ℝ)^3127
        have hw : |(1266196649/2500000000 : ℝ)|=(1266196649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1845370169/5000000000 : ℝ)|^4151 ≤ (26629067908767/100000000000000 : ℝ)^3127
        have hw : |(1845370169/5000000000 : ℝ)|=(1845370169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5147/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13971/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13971/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13971/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13971/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13971/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13971/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (277/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (4303294379/100000000000000000000 : ℝ) := by
    have hpowers : (277/100000 : ℝ)^8301 ≤ (4303294379/100000000000000000000 : ℝ)^2048 := by
      have hnat : (277 : ℕ)^8301*100000000000000000000^2048 ≤ 4303294379^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        277 100000 4303294379 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (277/100000 : ℝ)) (X := (4303294379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13971/50000 : ℝ) ^ (8301/2048 : ℝ) ≤ (8899760753223369/1562500000000000000 : ℝ) := by
    have hpowers : (13971/50000 : ℝ)^8301 ≤ (8899760753223369/1562500000000000000 : ℝ)^2048 := by
      have hnat : (13971 : ℕ)^8301*1562500000000000000^2048 ≤ 8899760753223369^2048*50000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13971 50000 8899760753223369 1562500000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13971/50000 : ℝ)) (X := (8899760753223369/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000004303294379/50000000000000000000 : ℝ) ≤ (500000000010617/500000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50000000004303294379/50000000000000000000 : ℝ)^2048 ≤ (500000000010617/500000000000000 : ℝ)^8301 := by
      have hnat : (50000000004303294379 : ℕ)^2048*500000000000000^8301 ≤ 500000000010617^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000004303294379 50000000000000000000 500000000010617 500000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000010617/500000000000000 : ℝ)) (X := (50000000004303294379/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20113916938501917999/20000000000000000000 : ℝ) ≤ (10014022590593823/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (20113916938501917999/20000000000000000000 : ℝ)^2048 ≤ (10014022590593823/10000000000000000 : ℝ)^8301 := by
      have hnat : (20113916938501917999 : ℕ)^2048*10000000000000000^8301 ≤ 10014022590593823^8301*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20113916938501917999 20000000000000000000 10014022590593823 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014022590593823/10000000000000000 : ℝ)) (X := (20113916938501917999/20000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (790149760753223369/781250000000000000 : ℝ) ≤ (5014022590487653/5000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (790149760753223369/781250000000000000 : ℝ)^2048 ≤ (5014022590487653/5000000000000000 : ℝ)^8301 := by
      have hnat : (790149760753223369 : ℕ)^2048*5000000000000000^8301 ≤ 5014022590487653^8301*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        790149760753223369 781250000000000000 5014022590487653 5000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014022590487653/5000000000000000 : ℝ)) (X := (790149760753223369/781250000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4303294379/100000000000000000000 : ℝ) ≤ ((138321115745401522259/138325000000000000000 : ℝ)+2*(14022590381483/2766500000000000 : ℝ)*(277/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (138321115745401522259/138325000000000000000 : ℝ)+2*(14022590381483/2766500000000000 : ℝ)*(277/100000 : ℝ)=(500000000010617/500000000000000 : ℝ) by norm_num, show 1+2*(4303294379/100000000000000000000 : ℝ)=(50000000004303294379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8899760753223369/1562500000000000000 : ℝ)+(4303294379/100000000000000000000 : ℝ) ≤ ((138321115745401522259/138325000000000000000 : ℝ)+(14022590381483/2766500000000000 : ℝ)*((13971/50000 : ℝ)+(277/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (138321115745401522259/138325000000000000000 : ℝ)+(14022590381483/2766500000000000 : ℝ)*((13971/50000 : ℝ)+(277/100000 : ℝ))=(10014022590593823/10000000000000000 : ℝ) by norm_num, show 1+(8899760753223369/1562500000000000000 : ℝ)+(4303294379/100000000000000000000 : ℝ)=(20113916938501917999/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8899760753223369/1562500000000000000 : ℝ) ≤ ((138321115745401522259/138325000000000000000 : ℝ)+2*(14022590381483/2766500000000000 : ℝ)*(13971/50000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (138321115745401522259/138325000000000000000 : ℝ)+2*(14022590381483/2766500000000000 : ℝ)*(13971/50000 : ℝ)=(5014022590487653/5000000000000000 : ℝ) by norm_num, show 1+2*(8899760753223369/1562500000000000000 : ℝ)=(790149760753223369/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138321115745401522259/138325000000000000000 : ℝ)*(X 1 0+X 2 0)+(14022590381483/2766500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (277/100000 : ℝ)) (hi := (13971/50000 : ℝ)) (c := (138321115745401522259/138325000000000000000 : ℝ)) (alpha := (14022590381483/2766500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138321115745401522259/138325000000000000000 : ℝ)*(X 0 1+X 2 1)+(14022590381483/2766500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (277/100000 : ℝ)) (hi := (13971/50000 : ℝ)) (c := (138321115745401522259/138325000000000000000 : ℝ)) (alpha := (14022590381483/2766500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138321115745401522259/138325000000000000000 : ℝ)*(X 0 2+X 1 2)+(14022590381483/2766500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (277/100000 : ℝ)) (hi := (13971/50000 : ℝ)) (c := (138321115745401522259/138325000000000000000 : ℝ)) (alpha := (14022590381483/2766500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109345911/10000000000 : ℝ)*X 0 0+(142760453/250000000 : ℝ)*X 0 1+(249764449/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420937719/10000000000 : ℝ)*X 1 0+(-499184937/2000000000 : ℝ)*X 1 1+(1248822243/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420938981/10000000000 : ℝ)*X 2 0+(499528777/1000000000 : ℝ)*X 2 1+(-499184913/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320220661/10000000000 : ℝ)*X 0 0+(458850597/1250000000 : ℝ)*X 0 1+(2542165481/5000000000 : ℝ)*X 0 2+(4320220661/10000000000 : ℝ)*X 1 0+(458850597/1250000000 : ℝ)*X 1 1+(2542165481/5000000000 : ℝ)*X 1 2+(4320220661/10000000000 : ℝ)*X 2 0+(458850597/1250000000 : ℝ)*X 2 1+(2542165481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527549803/2500000000 : ℝ)*X 0 0+(5005177199/10000000000 : ℝ)*X 0 1+(2850165967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309474383/2500000000 : ℝ)*X 1 0+(-895440687/5000000000 : ℝ)*X 1 1+(2850165871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618948779/5000000000 : ℝ)*X 2 0+(2850165941/5000000000 : ℝ)*X 2 1+(-1790881131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160952881/5000000000 : ℝ)*X 0 0+(1266196649/2500000000 : ℝ)*X 0 1+(1845370169/5000000000 : ℝ)*X 0 2+(2160952881/5000000000 : ℝ)*X 1 0+(1266196649/2500000000 : ℝ)*X 1 1+(1845370169/5000000000 : ℝ)*X 1 2+(2160952881/5000000000 : ℝ)*X 2 0+(1266196649/2500000000 : ℝ)*X 2 1+(1845370169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28664829746145478856966564727/6916250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55162007/25000000000000 : ℝ)*(base1) + (681619779/100000000000000 : ℝ)*(base19) + (1005721453/100000000000000 : ℝ)*(base23) + (1436187/100000000000000 : ℝ)*(base24) + (62449699/50000000000000 : ℝ)*(upper5) + (1052902727303883/100000000000000 : ℝ)*(major0) + (1052902727303883/100000000000000 : ℝ)*(major1) + (1052902727303883/100000000000000 : ℝ)*(major2) + (1398350164757561/100000000000000 : ℝ)*(sp0) + (699176260877883/50000000000000 : ℝ)*(sp1) + (87397012263619/6250000000000 : ℝ)*(sp2) + (88431419638603/12500000000000 : ℝ)*(sp3) + (814816503/25000000000000 : ℝ)*(sp4) + (267661641/50000000000000 : ℝ)*(sp7) + (353726056540067/50000000000000 : ℝ)*(f.failure) + (279670640675109/20000000000000 : ℝ)*(f.sum) + (7473171797967/17290625000000000000000000000 : ℝ)*base66 + (59881141636676081697/13832500000000000000000000000000000 : ℝ)*base67 + (93194977924166081697/13832500000000000000000000000000000 : ℝ)*base69 + (41578474251091081697/13832500000000000000000000000000000 : ℝ)*base71 + (78388683299961/138325000000000000000000000000 : ℝ)*base74 + (99588254795136081697/13832500000000000000000000000000000 : ℝ)*base75 + (89320268097816081697/13832500000000000000000000000000000 : ℝ)*base77 + (120373868130986081697/13832500000000000000000000000000000 : ℝ)*base79 + (1010333792002811/138325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12993451/5000000000000000000000 : ℝ)*base90 + (12993451/5000000000000000000000 : ℝ)*base92 + (12993451/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308490210803943460263906621/138325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (967559/3125000000000 : ℝ)*(base1) + (32549183/6250000000000 : ℝ)*(base19) + (272386437/50000000000000 : ℝ)*(base23) + (222853/500000000000 : ℝ)*(upper3) + (9395221/20000000000000 : ℝ)*(upper5) + (21663063630227/2000000000000 : ℝ)*(major0) + (21663063630227/2000000000000 : ℝ)*(major1) + (21663063630227/2000000000000 : ℝ)*(major2) + (15213993/800000000000 : ℝ)*(sp1) + (1191890629/50000000000000 : ℝ)*(sp2) + (719264365929957/50000000000000 : ℝ)*(sp4) + (1438526278361973/100000000000000 : ℝ)*(sp5) + (1438525772343893/100000000000000 : ℝ)*(sp6) + (181944389205827/25000000000000 : ℝ)*(sp7) + (181944396946299/25000000000000 : ℝ)*(f.failure) + (719264350449013/50000000000000 : ℝ)*(f.sum) + (9867194771329/2766500000000000000000000000 : ℝ)*base65 + (942567081218672793/276650000000000000000000000000000 : ℝ)*base67 + (102675082119227207/276650000000000000000000000000000 : ℝ)*base70 + (988348021501222793/276650000000000000000000000000000 : ℝ)*base71 + (26293068792429/5533000000000000000000000000 : ℝ)*base73 + (958105318972727207/276650000000000000000000000000000 : ℝ)*base76 + (1656946091672572793/276650000000000000000000000000000 : ℝ)*base77 + (2280554264058672793/276650000000000000000000000000000 : ℝ)*base79 + (453547635199/5533000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24094147/2500000000000000000000 : ℝ)*base90 + (24094147/2500000000000000000000 : ℝ)*base92 + (24094147/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1109_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5147/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s2_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432874619/2000000000 : ℝ)*x 0 + (5517195761/10000000000 : ℝ)*x 1 + (5153554603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432874619/2000000000 : ℝ)^4151 ≤ (6556062181841/50000000000000 : ℝ)^3127 := by
    have hnat : (432874619 : ℕ)^4151*50000000000000^3127 ≤ 6556062181841^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432874619 2000000000 6556062181841 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517195761/10000000000 : ℝ)^4151 ≤ (5676084093709/12500000000000 : ℝ)^3127 := by
    have hnat : (5517195761 : ℕ)^4151*12500000000000^3127 ≤ 5676084093709^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517195761 10000000000 5676084093709 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153554603/10000000000 : ℝ)^4151 ≤ (4147920288263/10000000000000 : ℝ)^3127 := by
    have hnat : (5153554603 : ℕ)^4151*10000000000000^3127 ≤ 4147920288263^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153554603 10000000000 4147920288263 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432874619/2000000000 : ℝ), (5517195761/10000000000 : ℝ), (5153554603/10000000000 : ℝ)] ![(6556062181841/50000000000000 : ℝ), (5676084093709/12500000000000 : ℝ), (4147920288263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432874619/2000000000 : ℝ)|^4151 ≤ (6556062181841/50000000000000 : ℝ)^3127
        have hw : |(-432874619/2000000000 : ℝ)|=(432874619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517195761/10000000000 : ℝ)|^4151 ≤ (5676084093709/12500000000000 : ℝ)^3127
        have hw : |(5517195761/10000000000 : ℝ)|=(5517195761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153554603/10000000000 : ℝ)|^4151 ≤ (4147920288263/10000000000000 : ℝ)^3127
        have hw : |(5153554603/10000000000 : ℝ)|=(5153554603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671911661/1250000000 : ℝ)*x 0 + (-2353678419/10000000000 : ℝ)*x 1 + (644194481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671911661/1250000000 : ℝ)^4151 ≤ (10966217571729/25000000000000 : ℝ)^3127 := by
    have hnat : (671911661 : ℕ)^4151*25000000000000^3127 ≤ 10966217571729^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671911661 1250000000 10966217571729 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353678419/10000000000 : ℝ)^4151 ≤ (14655913503769/100000000000000 : ℝ)^3127 := by
    have hnat : (2353678419 : ℕ)^4151*100000000000000^3127 ≤ 14655913503769^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353678419 10000000000 14655913503769 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644194481/1250000000 : ℝ)^4151 ≤ (20739608092327/50000000000000 : ℝ)^3127 := by
    have hnat : (644194481 : ℕ)^4151*50000000000000^3127 ≤ 20739608092327^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644194481 1250000000 20739608092327 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671911661/1250000000 : ℝ), (-2353678419/10000000000 : ℝ), (644194481/1250000000 : ℝ)] ![(10966217571729/25000000000000 : ℝ), (14655913503769/100000000000000 : ℝ), (20739608092327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671911661/1250000000 : ℝ)|^4151 ≤ (10966217571729/25000000000000 : ℝ)^3127
        have hw : |(671911661/1250000000 : ℝ)|=(671911661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2353678419/10000000000 : ℝ)|^4151 ≤ (14655913503769/100000000000000 : ℝ)^3127
        have hw : |(-2353678419/10000000000 : ℝ)|=(2353678419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644194481/1250000000 : ℝ)|^4151 ≤ (20739608092327/50000000000000 : ℝ)^3127
        have hw : |(644194481/1250000000 : ℝ)|=(644194481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075058647/2000000000 : ℝ)*x 0 + (1030711181/2000000000 : ℝ)*x 1 + (-147104901/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075058647/2000000000 : ℝ)^4151 ≤ (43864869712779/100000000000000 : ℝ)^3127 := by
    have hnat : (1075058647 : ℕ)^4151*100000000000000^3127 ≤ 43864869712779^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075058647 2000000000 43864869712779 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030711181/2000000000 : ℝ)^4151 ≤ (41479216793663/100000000000000 : ℝ)^3127 := by
    have hnat : (1030711181 : ℕ)^4151*100000000000000^3127 ≤ 41479216793663^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030711181 2000000000 41479216793663 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147104901/625000000 : ℝ)^4151 ≤ (14655913478971/100000000000000 : ℝ)^3127 := by
    have hnat : (147104901 : ℕ)^4151*100000000000000^3127 ≤ 14655913478971^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147104901 625000000 14655913478971 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075058647/2000000000 : ℝ), (1030711181/2000000000 : ℝ), (-147104901/625000000 : ℝ)] ![(43864869712779/100000000000000 : ℝ), (41479216793663/100000000000000 : ℝ), (14655913478971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075058647/2000000000 : ℝ)|^4151 ≤ (43864869712779/100000000000000 : ℝ)^3127
        have hw : |(1075058647/2000000000 : ℝ)|=(1075058647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030711181/2000000000 : ℝ)|^4151 ≤ (41479216793663/100000000000000 : ℝ)^3127
        have hw : |(1030711181/2000000000 : ℝ)|=(1030711181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147104901/625000000 : ℝ)|^4151 ≤ (14655913478971/100000000000000 : ℝ)^3127
        have hw : |(-147104901/625000000 : ℝ)|=(147104901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4357884057/10000000000 : ℝ)*x 0 + (1003323871/2500000000 : ℝ)*x 1 + (2366033817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357884057/10000000000 : ℝ)^4151 ≤ (33200844036609/100000000000000 : ℝ)^3127 := by
    have hnat : (4357884057 : ℕ)^4151*100000000000000^3127 ≤ 33200844036609^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357884057 10000000000 33200844036609 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003323871/2500000000 : ℝ)^4151 ≤ (1860113757231/6250000000000 : ℝ)^3127 := by
    have hnat : (1003323871 : ℕ)^4151*6250000000000^3127 ≤ 1860113757231^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003323871 2500000000 1860113757231 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2366033817/5000000000 : ℝ)^4151 ≤ (37037335832667/100000000000000 : ℝ)^3127 := by
    have hnat : (2366033817 : ℕ)^4151*100000000000000^3127 ≤ 37037335832667^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366033817 5000000000 37037335832667 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357884057/10000000000 : ℝ), (1003323871/2500000000 : ℝ), (2366033817/5000000000 : ℝ)] ![(33200844036609/100000000000000 : ℝ), (1860113757231/6250000000000 : ℝ), (37037335832667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357884057/10000000000 : ℝ)|^4151 ≤ (33200844036609/100000000000000 : ℝ)^3127
        have hw : |(4357884057/10000000000 : ℝ)|=(4357884057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003323871/2500000000 : ℝ)|^4151 ≤ (1860113757231/6250000000000 : ℝ)^3127
        have hw : |(1003323871/2500000000 : ℝ)|=(1003323871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2366033817/5000000000 : ℝ)|^4151 ≤ (37037335832667/100000000000000 : ℝ)^3127
        have hw : |(2366033817/5000000000 : ℝ)|=(2366033817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082242477/5000000000 : ℝ)*x 0 + (80564391/156250000 : ℝ)*x 1 + (2757301633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082242477/5000000000 : ℝ)^4151 ≤ (13113023944927/100000000000000 : ℝ)^3127 := by
    have hnat : (1082242477 : ℕ)^4151*100000000000000^3127 ≤ 13113023944927^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082242477 5000000000 13113023944927 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80564391/156250000 : ℝ)^4151 ≤ (4150662567521/10000000000000 : ℝ)^3127 := by
    have hnat : (80564391 : ℕ)^4151*10000000000000^3127 ≤ 4150662567521^3127*156250000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80564391 156250000 4150662567521 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757301633/5000000000 : ℝ)^4151 ≤ (45380350367727/100000000000000 : ℝ)^3127 := by
    have hnat : (2757301633 : ℕ)^4151*100000000000000^3127 ≤ 45380350367727^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757301633 5000000000 45380350367727 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082242477/5000000000 : ℝ), (80564391/156250000 : ℝ), (2757301633/5000000000 : ℝ)] ![(13113023944927/100000000000000 : ℝ), (4150662567521/10000000000000 : ℝ), (45380350367727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082242477/5000000000 : ℝ)|^4151 ≤ (13113023944927/100000000000000 : ℝ)^3127
        have hw : |(-1082242477/5000000000 : ℝ)|=(1082242477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80564391/156250000 : ℝ)|^4151 ≤ (4150662567521/10000000000000 : ℝ)^3127
        have hw : |(80564391/156250000 : ℝ)|=(80564391/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757301633/5000000000 : ℝ)|^4151 ≤ (45380350367727/100000000000000 : ℝ)^3127
        have hw : |(2757301633/5000000000 : ℝ)|=(2757301633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056646601/2000000000 : ℝ)*x 0 + (-1992630399/10000000000 : ℝ)*x 1 + (110292067/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056646601/2000000000 : ℝ)^4151 ≤ (10717602439307/25000000000000 : ℝ)^3127 := by
    have hnat : (1056646601 : ℕ)^4151*25000000000000^3127 ≤ 10717602439307^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056646601 2000000000 10717602439307 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992630399/10000000000 : ℝ)^4151 ≤ (2349847789877/20000000000000 : ℝ)^3127 := by
    have hnat : (1992630399 : ℕ)^4151*20000000000000^3127 ≤ 2349847789877^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992630399 10000000000 2349847789877 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110292067/200000000 : ℝ)^4151 ≤ (5672543910667/12500000000000 : ℝ)^3127 := by
    have hnat : (110292067 : ℕ)^4151*12500000000000^3127 ≤ 5672543910667^3127*200000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110292067 200000000 5672543910667 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056646601/2000000000 : ℝ), (-1992630399/10000000000 : ℝ), (110292067/200000000 : ℝ)] ![(10717602439307/25000000000000 : ℝ), (2349847789877/20000000000000 : ℝ), (5672543910667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056646601/2000000000 : ℝ)|^4151 ≤ (10717602439307/25000000000000 : ℝ)^3127
        have hw : |(1056646601/2000000000 : ℝ)|=(1056646601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992630399/10000000000 : ℝ)|^4151 ≤ (2349847789877/20000000000000 : ℝ)^3127
        have hw : |(-1992630399/10000000000 : ℝ)|=(1992630399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110292067/200000000 : ℝ)|^4151 ≤ (5672543910667/12500000000000 : ℝ)^3127
        have hw : |(110292067/200000000 : ℝ)|=(110292067/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2641616571/5000000000 : ℝ)*x 0 + (2757301647/5000000000 : ℝ)*x 1 + (-124539393/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641616571/5000000000 : ℝ)^4151 ≤ (21435205616473/50000000000000 : ℝ)^3127 := by
    have hnat : (2641616571 : ℕ)^4151*50000000000000^3127 ≤ 21435205616473^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641616571 5000000000 21435205616473 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757301647/5000000000 : ℝ)^4151 ≤ (11345087668399/25000000000000 : ℝ)^3127 := by
    have hnat : (2757301647 : ℕ)^4151*25000000000000^3127 ≤ 11345087668399^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757301647 5000000000 11345087668399 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124539393/625000000 : ℝ)^4151 ≤ (11749238080563/100000000000000 : ℝ)^3127 := by
    have hnat : (124539393 : ℕ)^4151*100000000000000^3127 ≤ 11749238080563^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124539393 625000000 11749238080563 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641616571/5000000000 : ℝ), (2757301647/5000000000 : ℝ), (-124539393/625000000 : ℝ)] ![(21435205616473/50000000000000 : ℝ), (11345087668399/25000000000000 : ℝ), (11749238080563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641616571/5000000000 : ℝ)|^4151 ≤ (21435205616473/50000000000000 : ℝ)^3127
        have hw : |(2641616571/5000000000 : ℝ)|=(2641616571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757301647/5000000000 : ℝ)|^4151 ≤ (11345087668399/25000000000000 : ℝ)^3127
        have hw : |(2757301647/5000000000 : ℝ)|=(2757301647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124539393/625000000 : ℝ)|^4151 ≤ (11749238080563/100000000000000 : ℝ)^3127
        have hw : |(-124539393/625000000 : ℝ)|=(124539393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s2_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544763313/1250000000 : ℝ)*x 0 + (4726995961/10000000000 : ℝ)*x 1 + (4018417751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544763313/1250000000 : ℝ)^4151 ≤ (16601546878353/50000000000000 : ℝ)^3127 := by
    have hnat : (544763313 : ℕ)^4151*50000000000000^3127 ≤ 16601546878353^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544763313 1250000000 16601546878353 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4726995961/10000000000 : ℝ)^4151 ≤ (3698465062999/10000000000000 : ℝ)^3127 := by
    have hnat : (4726995961 : ℕ)^4151*10000000000000^3127 ≤ 3698465062999^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726995961 10000000000 3698465062999 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018417751/10000000000 : ℝ)^4151 ≤ (7453063898353/25000000000000 : ℝ)^3127 := by
    have hnat : (4018417751 : ℕ)^4151*25000000000000^3127 ≤ 7453063898353^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018417751 10000000000 7453063898353 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544763313/1250000000 : ℝ), (4726995961/10000000000 : ℝ), (4018417751/10000000000 : ℝ)] ![(16601546878353/50000000000000 : ℝ), (3698465062999/10000000000000 : ℝ), (7453063898353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544763313/1250000000 : ℝ)|^4151 ≤ (16601546878353/50000000000000 : ℝ)^3127
        have hw : |(544763313/1250000000 : ℝ)|=(544763313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4726995961/10000000000 : ℝ)|^4151 ≤ (3698465062999/10000000000000 : ℝ)^3127
        have hw : |(4726995961/10000000000 : ℝ)|=(4726995961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018417751/10000000000 : ℝ)|^4151 ≤ (7453063898353/25000000000000 : ℝ)^3127
        have hw : |(4018417751/10000000000 : ℝ)|=(4018417751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5147/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4459/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16603/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5147/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5147/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5147/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5147/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5147/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5147/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5463/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (763005268696693/100000000000000000000 : ℝ) := by
    have hpowers : (5463/100000 : ℝ)^8301 ≤ (763005268696693/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5463 : ℕ)^8301*100000000000000000000^2048 ≤ 763005268696693^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5463 100000 763005268696693 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5463/100000 : ℝ)) (X := (763005268696693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5147/25000 : ℝ) ^ (8301/2048 : ℝ) ≤ (165167791085008621/100000000000000000000 : ℝ) := by
    have hpowers : (5147/25000 : ℝ)^8301 ≤ (165167791085008621/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5147 : ℕ)^8301*100000000000000000000^2048 ≤ 165167791085008621^2048*25000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5147 25000 165167791085008621 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5147/25000 : ℝ)) (X := (165167791085008621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000763005268696693/50000000000000000000 : ℝ) ≤ (2500009412274479/2500000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50000763005268696693/50000000000000000000 : ℝ)^2048 ≤ (2500009412274479/2500000000000000 : ℝ)^8301 := by
      have hnat : (50000763005268696693 : ℕ)^2048*2500000000000000^8301 ≤ 2500009412274479^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000763005268696693 50000000000000000000 2500009412274479 2500000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009412274479/2500000000000000 : ℝ)) (X := (50000763005268696693/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50082965398176852657/50000000000000000000 : ℝ) ≤ (5002045621596543/5000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50082965398176852657/50000000000000000000 : ℝ)^2048 ≤ (5002045621596543/5000000000000000 : ℝ)^8301 := by
      have hnat : (50082965398176852657 : ℕ)^2048*5000000000000000^8301 ≤ 5002045621596543^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50082965398176852657 50000000000000000000 5002045621596543 5000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002045621596543/5000000000000000 : ℝ)) (X := (50082965398176852657/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50165167791085008621/50000000000000000000 : ℝ) ≤ (156377263082629/156250000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50165167791085008621/50000000000000000000 : ℝ)^2048 ≤ (156377263082629/156250000000000 : ℝ)^8301 := by
      have hnat : (50165167791085008621 : ℕ)^2048*156250000000000^8301 ≤ 156377263082629^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50165167791085008621 50000000000000000000 156377263082629 156250000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156377263082629/156250000000000 : ℝ)) (X := (50165167791085008621/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(763005268696693/100000000000000000000 : ℝ) ≤ ((1890078498419026901/1890625000000000000 : ℝ)+2*(405359409517/151250000000000 : ℝ)*(5463/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1890078498419026901/1890625000000000000 : ℝ)+2*(405359409517/151250000000000 : ℝ)*(5463/100000 : ℝ)=(2500009412274479/2500000000000000 : ℝ) by norm_num, show 1+2*(763005268696693/100000000000000000000 : ℝ)=(50000763005268696693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(165167791085008621/100000000000000000000 : ℝ)+(763005268696693/100000000000000000000 : ℝ) ≤ ((1890078498419026901/1890625000000000000 : ℝ)+(405359409517/151250000000000 : ℝ)*((5147/25000 : ℝ)+(5463/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (1890078498419026901/1890625000000000000 : ℝ)+(405359409517/151250000000000 : ℝ)*((5147/25000 : ℝ)+(5463/100000 : ℝ))=(5002045621596543/5000000000000000 : ℝ) by norm_num, show 1+(165167791085008621/100000000000000000000 : ℝ)+(763005268696693/100000000000000000000 : ℝ)=(50082965398176852657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(165167791085008621/100000000000000000000 : ℝ) ≤ ((1890078498419026901/1890625000000000000 : ℝ)+2*(405359409517/151250000000000 : ℝ)*(5147/25000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1890078498419026901/1890625000000000000 : ℝ)+2*(405359409517/151250000000000 : ℝ)*(5147/25000 : ℝ)=(156377263082629/156250000000000 : ℝ) by norm_num, show 1+2*(165167791085008621/100000000000000000000 : ℝ)=(50165167791085008621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1890078498419026901/1890625000000000000 : ℝ)*(X 1 0+X 2 0)+(405359409517/151250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5463/100000 : ℝ)) (hi := (5147/25000 : ℝ)) (c := (1890078498419026901/1890625000000000000 : ℝ)) (alpha := (405359409517/151250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1890078498419026901/1890625000000000000 : ℝ)*(X 0 1+X 2 1)+(405359409517/151250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5463/100000 : ℝ)) (hi := (5147/25000 : ℝ)) (c := (1890078498419026901/1890625000000000000 : ℝ)) (alpha := (405359409517/151250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1890078498419026901/1890625000000000000 : ℝ)*(X 0 2+X 1 2)+(405359409517/151250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5463/100000 : ℝ)) (hi := (5147/25000 : ℝ)) (c := (1890078498419026901/1890625000000000000 : ℝ)) (alpha := (405359409517/151250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432874619/2000000000 : ℝ)*X 0 0+(5517195761/10000000000 : ℝ)*X 0 1+(5153554603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671911661/1250000000 : ℝ)*X 1 0+(-2353678419/10000000000 : ℝ)*X 1 1+(644194481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075058647/2000000000 : ℝ)*X 2 0+(1030711181/2000000000 : ℝ)*X 2 1+(-147104901/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357884057/10000000000 : ℝ)*X 0 0+(1003323871/2500000000 : ℝ)*X 0 1+(2366033817/5000000000 : ℝ)*X 0 2+(4357884057/10000000000 : ℝ)*X 1 0+(1003323871/2500000000 : ℝ)*X 1 1+(2366033817/5000000000 : ℝ)*X 1 2+(4357884057/10000000000 : ℝ)*X 2 0+(1003323871/2500000000 : ℝ)*X 2 1+(2366033817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082242477/5000000000 : ℝ)*X 0 0+(80564391/156250000 : ℝ)*X 0 1+(2757301633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056646601/2000000000 : ℝ)*X 1 0+(-1992630399/10000000000 : ℝ)*X 1 1+(110292067/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641616571/5000000000 : ℝ)*X 2 0+(2757301647/5000000000 : ℝ)*X 2 1+(-124539393/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544763313/1250000000 : ℝ)*X 0 0+(4726995961/10000000000 : ℝ)*X 0 1+(4018417751/10000000000 : ℝ)*X 0 2+(544763313/1250000000 : ℝ)*X 1 0+(4726995961/10000000000 : ℝ)*X 1 1+(4018417751/10000000000 : ℝ)*X 1 2+(544763313/1250000000 : ℝ)*X 2 0+(4726995961/10000000000 : ℝ)*X 2 1+(4018417751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497262568835761804989872463/47265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174782377/12500000000000 : ℝ)*(base19) + (1160607209/100000000000000 : ℝ)*(base23) + (128290891/50000000000000 : ℝ)*(upper3) + (113169783/100000000000000 : ℝ)*(upper4) + (45612719/50000000000000 : ℝ)*(upper5) + (517660795634227/25000000000000 : ℝ)*(major0) + (517660795634227/25000000000000 : ℝ)*(major1) + (517660795634227/25000000000000 : ℝ)*(major2) + (109999455980761/4000000000000 : ℝ)*(sp0) + (2750006146680491/100000000000000 : ℝ)*(sp1) + (1375003192166149/50000000000000 : ℝ)*(sp2) + (1391269138037907/100000000000000 : ℝ)*(sp3) + (21145420481/100000000000000 : ℝ)*(sp4) + (2332852461/25000000000000 : ℝ)*(sp7) + (1391278469447751/100000000000000 : ℝ)*(f.failure) + (1375003772469753/50000000000000 : ℝ)*(f.sum) + (37136577168189/7562500000000000000000000000 : ℝ)*base66 + (73564592630468701/23632812500000000000000000000000 : ℝ)*base67 + (106353062945898413/11816406250000000000000000000000 : ℝ)*base69 + (796165443072509/369262695312500000000000000000 : ℝ)*base71 + (22101386718997/15125000000000000000000000000 : ℝ)*base73 + (351627455242578223/47265625000000000000000000000000 : ℝ)*base76 + (176715191039843701/23632812500000000000000000000000 : ℝ)*base77 + (7286388426953223/47265625000000000000000000000000 : ℝ)*base80 + (19076513166311/7562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (65075503/10000000000000000000000 : ℝ)*base90 + (65075503/10000000000000000000000 : ℝ)*base92 + (65075503/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (358582465027987343003927559/47265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (759239561/50000000000000 : ℝ)*(base19) + (1739367331/100000000000000 : ℝ)*(base23) + (20276371/10000000000000 : ℝ)*(upper3) + (52927223/100000000000000 : ℝ)*(lower4) + (146200679/100000000000000 : ℝ)*(upper5) + (2100407428564847/100000000000000 : ℝ)*(major0) + (2100407428564847/100000000000000 : ℝ)*(major1) + (2100407428564847/100000000000000 : ℝ)*(major2) + (6948760459/50000000000000 : ℝ)*(sp1) + (16673619739/100000000000000 : ℝ)*(sp2) + (1394768673247309/50000000000000 : ℝ)*(sp4) + (1394760965247289/50000000000000 : ℝ)*(sp5) + (697379733376887/25000000000000 : ℝ)*(sp6) + (1411277257750467/100000000000000 : ℝ)*(sp7) + (1411277257750467/100000000000000 : ℝ)*(f.failure) + (1394768673247309/50000000000000 : ℝ)*(f.sum) + (29239292491649/7562500000000000000000000000 : ℝ)*base65 + (1151626651297499147/189062500000000000000000000000000 : ℝ)*base67 + (193694735899375853/189062500000000000000000000000000 : ℝ)*base70 + (1985322318824061647/189062500000000000000000000000000 : ℝ)*base71 + (49540334237423/15125000000000000000000000000 : ℝ)*base73 + (1208649439888124147/189062500000000000000000000000000 : ℝ)*base75 + (646424004688124147/189062500000000000000000000000000 : ℝ)*base77 + (726231663680311647/189062500000000000000000000000000 : ℝ)*base79 + (18436769195827/15125000000000000000000000000 : ℝ)*base82 + (32024651/10000000000000000000000 : ℝ)*base90 + (32024651/10000000000000000000000 : ℝ)*base92 + (32024651/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1109_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5147/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1109_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1109_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1109_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1109_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
