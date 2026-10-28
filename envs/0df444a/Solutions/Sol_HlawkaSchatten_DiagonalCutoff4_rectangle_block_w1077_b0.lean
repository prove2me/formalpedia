-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:14:26.396764+00:00
-- url     : https://prove2.me/submissions/c335f8a0-b46d-431c-b6aa-1f75395e1b96

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
theorem support_rectangle_w1077_s0_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95627737/500000000 : ℝ)*x 0 + (6069475693/10000000000 : ℝ)*x 1 + (2386098479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95627737/500000000 : ℝ)^4135 ≤ (2219135202591/20000000000000 : ℝ)^3111 := by
    have hnat : (95627737 : ℕ)^4135*20000000000000^3111 ≤ 2219135202591^3111*500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95627737 500000000 2219135202591 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6069475693/10000000000 : ℝ)^4135 ≤ (51496105515861/100000000000000 : ℝ)^3111 := by
    have hnat : (6069475693 : ℕ)^4135*100000000000000^3111 ≤ 51496105515861^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6069475693 10000000000 51496105515861 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386098479/5000000000 : ℝ)^4135 ≤ (3740821845327/10000000000000 : ℝ)^3111 := by
    have hnat : (2386098479 : ℕ)^4135*10000000000000^3111 ≤ 3740821845327^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386098479 5000000000 3740821845327 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95627737/500000000 : ℝ), (6069475693/10000000000 : ℝ), (2386098479/5000000000 : ℝ)] ![(2219135202591/20000000000000 : ℝ), (51496105515861/100000000000000 : ℝ), (3740821845327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95627737/500000000 : ℝ)|^4135 ≤ (2219135202591/20000000000000 : ℝ)^3111
        have hw : |(-95627737/500000000 : ℝ)|=(95627737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6069475693/10000000000 : ℝ)|^4135 ≤ (51496105515861/100000000000000 : ℝ)^3111
        have hw : |(6069475693/10000000000 : ℝ)|=(6069475693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386098479/5000000000 : ℝ)|^4135 ≤ (3740821845327/10000000000000 : ℝ)^3111
        have hw : |(2386098479/5000000000 : ℝ)|=(2386098479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5520454007/10000000000 : ℝ)*x 0 + (-2658948629/10000000000 : ℝ)*x 1 + (29826231/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520454007/10000000000 : ℝ)^4135 ≤ (11349706175609/25000000000000 : ℝ)^3111 := by
    have hnat : (5520454007 : ℕ)^4135*25000000000000^3111 ≤ 11349706175609^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520454007 10000000000 11349706175609 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2658948629/10000000000 : ℝ)^4135 ≤ (4298239202537/25000000000000 : ℝ)^3111 := by
    have hnat : (2658948629 : ℕ)^4135*25000000000000^3111 ≤ 4298239202537^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2658948629 10000000000 4298239202537 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29826231/62500000 : ℝ)^4135 ≤ (9352054618527/25000000000000 : ℝ)^3111 := by
    have hnat : (29826231 : ℕ)^4135*25000000000000^3111 ≤ 9352054618527^3111*62500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29826231 62500000 9352054618527 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520454007/10000000000 : ℝ), (-2658948629/10000000000 : ℝ), (29826231/62500000 : ℝ)] ![(11349706175609/25000000000000 : ℝ), (4298239202537/25000000000000 : ℝ), (9352054618527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520454007/10000000000 : ℝ)|^4135 ≤ (11349706175609/25000000000000 : ℝ)^3111
        have hw : |(5520454007/10000000000 : ℝ)|=(5520454007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2658948629/10000000000 : ℝ)|^4135 ≤ (4298239202537/25000000000000 : ℝ)^3111
        have hw : |(-2658948629/10000000000 : ℝ)|=(2658948629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29826231/62500000 : ℝ)|^4135 ≤ (9352054618527/25000000000000 : ℝ)^3111
        have hw : |(29826231/62500000 : ℝ)|=(29826231/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2760227003/5000000000 : ℝ)*x 0 + (1193049241/2500000000 : ℝ)*x 1 + (-21271589/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760227003/5000000000 : ℝ)^4135 ≤ (22699412345753/50000000000000 : ℝ)^3111 := by
    have hnat : (2760227003 : ℕ)^4135*50000000000000^3111 ≤ 22699412345753^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760227003 5000000000 22699412345753 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193049241/2500000000 : ℝ)^4135 ≤ (37408218515783/100000000000000 : ℝ)^3111 := by
    have hnat : (1193049241 : ℕ)^4135*100000000000000^3111 ≤ 37408218515783^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193049241 2500000000 37408218515783 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21271589/80000000 : ℝ)^4135 ≤ (1719295677577/10000000000000 : ℝ)^3111 := by
    have hnat : (21271589 : ℕ)^4135*10000000000000^3111 ≤ 1719295677577^3111*80000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21271589 80000000 1719295677577 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760227003/5000000000 : ℝ), (1193049241/2500000000 : ℝ), (-21271589/80000000 : ℝ)] ![(22699412345753/50000000000000 : ℝ), (37408218515783/100000000000000 : ℝ), (1719295677577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760227003/5000000000 : ℝ)|^4135 ≤ (22699412345753/50000000000000 : ℝ)^3111
        have hw : |(2760227003/5000000000 : ℝ)|=(2760227003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193049241/2500000000 : ℝ)|^4135 ≤ (37408218515783/100000000000000 : ℝ)^3111
        have hw : |(1193049241/2500000000 : ℝ)|=(1193049241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21271589/80000000 : ℝ)|^4135 ≤ (1719295677577/10000000000000 : ℝ)^3111
        have hw : |(-21271589/80000000 : ℝ)|=(21271589/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131446887/312500000 : ℝ)*x 0 + (390535577/1250000000 : ℝ)*x 1 + (709040443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131446887/312500000 : ℝ)^4135 ≤ (31630446842409/100000000000000 : ℝ)^3111 := by
    have hnat : (131446887 : ℕ)^4135*100000000000000^3111 ≤ 31630446842409^3111*312500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131446887 312500000 31630446842409 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390535577/1250000000 : ℝ)^4135 ≤ (21303228056381/100000000000000 : ℝ)^3111 := by
    have hnat : (390535577 : ℕ)^4135*100000000000000^3111 ≤ 21303228056381^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390535577 1250000000 21303228056381 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709040443/1250000000 : ℝ)^4135 ≤ (5883290636429/12500000000000 : ℝ)^3111 := by
    have hnat : (709040443 : ℕ)^4135*12500000000000^3111 ≤ 5883290636429^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709040443 1250000000 5883290636429 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131446887/312500000 : ℝ), (390535577/1250000000 : ℝ), (709040443/1250000000 : ℝ)] ![(31630446842409/100000000000000 : ℝ), (21303228056381/100000000000000 : ℝ), (5883290636429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131446887/312500000 : ℝ)|^4135 ≤ (31630446842409/100000000000000 : ℝ)^3111
        have hw : |(131446887/312500000 : ℝ)|=(131446887/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(390535577/1250000000 : ℝ)|^4135 ≤ (21303228056381/100000000000000 : ℝ)^3111
        have hw : |(390535577/1250000000 : ℝ)|=(390535577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709040443/1250000000 : ℝ)|^4135 ≤ (5883290636429/12500000000000 : ℝ)^3111
        have hw : |(709040443/1250000000 : ℝ)|=(709040443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479473701/2500000000 : ℝ)*x 0 + (4805689611/10000000000 : ℝ)*x 1 + (754351297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479473701/2500000000 : ℝ)^4135 ≤ (445474904059/4000000000000 : ℝ)^3111 := by
    have hnat : (479473701 : ℕ)^4135*4000000000000^3111 ≤ 445474904059^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479473701 2500000000 445474904059 4000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805689611/10000000000 : ℝ)^4135 ≤ (18878789668527/50000000000000 : ℝ)^3111 := by
    have hnat : (4805689611 : ℕ)^4135*50000000000000^3111 ≤ 18878789668527^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805689611 10000000000 18878789668527 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754351297/1250000000 : ℝ)^4135 ≤ (25552774022623/50000000000000 : ℝ)^3111 := by
    have hnat : (754351297 : ℕ)^4135*50000000000000^3111 ≤ 25552774022623^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754351297 1250000000 25552774022623 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479473701/2500000000 : ℝ), (4805689611/10000000000 : ℝ), (754351297/1250000000 : ℝ)] ![(445474904059/4000000000000 : ℝ), (18878789668527/50000000000000 : ℝ), (25552774022623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479473701/2500000000 : ℝ)|^4135 ≤ (445474904059/4000000000000 : ℝ)^3111
        have hw : |(-479473701/2500000000 : ℝ)|=(479473701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805689611/10000000000 : ℝ)|^4135 ≤ (18878789668527/50000000000000 : ℝ)^3111
        have hw : |(4805689611/10000000000 : ℝ)|=(4805689611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754351297/1250000000 : ℝ)|^4135 ≤ (25552774022623/50000000000000 : ℝ)^3111
        have hw : |(754351297/1250000000 : ℝ)|=(754351297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2584146069/5000000000 : ℝ)*x 0 + (-698169339/5000000000 : ℝ)*x 1 + (6034808377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584146069/5000000000 : ℝ)^4135 ≤ (41590478297831/100000000000000 : ℝ)^3111 := by
    have hnat : (2584146069 : ℕ)^4135*100000000000000^3111 ≤ 41590478297831^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584146069 5000000000 41590478297831 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698169339/5000000000 : ℝ)^4135 ≤ (7303996145983/100000000000000 : ℝ)^3111 := by
    have hnat : (698169339 : ℕ)^4135*100000000000000^3111 ≤ 7303996145983^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698169339 5000000000 7303996145983 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6034808377/10000000000 : ℝ)^4135 ≤ (51105525544719/100000000000000 : ℝ)^3111 := by
    have hnat : (6034808377 : ℕ)^4135*100000000000000^3111 ≤ 51105525544719^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034808377 10000000000 51105525544719 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584146069/5000000000 : ℝ), (-698169339/5000000000 : ℝ), (6034808377/10000000000 : ℝ)] ![(41590478297831/100000000000000 : ℝ), (7303996145983/100000000000000 : ℝ), (51105525544719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584146069/5000000000 : ℝ)|^4135 ≤ (41590478297831/100000000000000 : ℝ)^3111
        have hw : |(2584146069/5000000000 : ℝ)|=(2584146069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698169339/5000000000 : ℝ)|^4135 ≤ (7303996145983/100000000000000 : ℝ)^3111
        have hw : |(-698169339/5000000000 : ℝ)|=(698169339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6034808377/10000000000 : ℝ)|^4135 ≤ (51105525544719/100000000000000 : ℝ)^3111
        have hw : |(6034808377/10000000000 : ℝ)|=(6034808377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2584146017/5000000000 : ℝ)*x 0 + (6034809913/10000000000 : ℝ)*x 1 + (-27926727/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584146017/5000000000 : ℝ)^4135 ≤ (10397619296361/25000000000000 : ℝ)^3111 := by
    have hnat : (2584146017 : ℕ)^4135*25000000000000^3111 ≤ 10397619296361^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584146017 5000000000 10397619296361 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6034809913/10000000000 : ℝ)^4135 ≤ (6388192854221/12500000000000 : ℝ)^3111 := by
    have hnat : (6034809913 : ℕ)^4135*12500000000000^3111 ≤ 6388192854221^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034809913 10000000000 6388192854221 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27926727/200000000 : ℝ)^4135 ≤ (7303979960409/100000000000000 : ℝ)^3111 := by
    have hnat : (27926727 : ℕ)^4135*100000000000000^3111 ≤ 7303979960409^3111*200000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27926727 200000000 7303979960409 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584146017/5000000000 : ℝ), (6034809913/10000000000 : ℝ), (-27926727/200000000 : ℝ)] ![(10397619296361/25000000000000 : ℝ), (6388192854221/12500000000000 : ℝ), (7303979960409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584146017/5000000000 : ℝ)|^4135 ≤ (10397619296361/25000000000000 : ℝ)^3111
        have hw : |(2584146017/5000000000 : ℝ)|=(2584146017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6034809913/10000000000 : ℝ)|^4135 ≤ (6388192854221/12500000000000 : ℝ)^3111
        have hw : |(6034809913/10000000000 : ℝ)|=(6034809913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27926727/200000000 : ℝ)|^4135 ≤ (7303979960409/100000000000000 : ℝ)^3111
        have hw : |(-27926727/200000000 : ℝ)|=(27926727/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s0_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105419681/250000000 : ℝ)*x 0 + (1121307337/2000000000 : ℝ)*x 1 + (638474863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105419681/250000000 : ℝ)^4135 ≤ (31735305407799/100000000000000 : ℝ)^3111 := by
    have hnat : (105419681 : ℕ)^4135*100000000000000^3111 ≤ 31735305407799^3111*250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105419681 250000000 31735305407799 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121307337/2000000000 : ℝ)^4135 ≤ (23171084627417/50000000000000 : ℝ)^3111 := by
    have hnat : (1121307337 : ℕ)^4135*50000000000000^3111 ≤ 23171084627417^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121307337 2000000000 23171084627417 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638474863/2000000000 : ℝ)^4135 ≤ (1096126266269/5000000000000 : ℝ)^3111 := by
    have hnat : (638474863 : ℕ)^4135*5000000000000^3111 ≤ 1096126266269^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638474863 2000000000 1096126266269 5000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105419681/250000000 : ℝ), (1121307337/2000000000 : ℝ), (638474863/2000000000 : ℝ)] ![(31735305407799/100000000000000 : ℝ), (23171084627417/50000000000000 : ℝ), (1096126266269/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105419681/250000000 : ℝ)|^4135 ≤ (31735305407799/100000000000000 : ℝ)^3111
        have hw : |(105419681/250000000 : ℝ)|=(105419681/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121307337/2000000000 : ℝ)|^4135 ≤ (23171084627417/50000000000000 : ℝ)^3111
        have hw : |(1121307337/2000000000 : ℝ)|=(1121307337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638474863/2000000000 : ℝ)|^4135 ≤ (1096126266269/5000000000000 : ℝ)^3111
        have hw : |(638474863/2000000000 : ℝ)|=(638474863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8269/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8269 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8269*1^2048 ≤ 0^2048*1^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8269/2048 : ℝ) ≤ (618327215584867769/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8269 ≤ (618327215584867769/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8269*25000000000000000000^2048 ≤ 618327215584867769^2048*5^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 618327215584867769 25000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (618327215584867769/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8269 := by
      have hnat : (1 : ℕ)^2048*1^8269 ≤ 1^8269*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25618327215584867769/25000000000000000000 : ℝ) ≤ (1257586890257757/1250000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (25618327215584867769/25000000000000000000 : ℝ)^2048 ≤ (1257586890257757/1250000000000000 : ℝ)^8269 := by
      have hnat : (25618327215584867769 : ℕ)^2048*1250000000000000^8269 ≤ 1257586890257757^8269*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25618327215584867769 25000000000000000000 1257586890257757 1250000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257586890257757/1250000000000000 : ℝ)) (X := (25618327215584867769/25000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13118327215584867769/12500000000000000000 : ℝ) ≤ (632586890257757/625000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (13118327215584867769/12500000000000000000 : ℝ)^2048 ≤ (632586890257757/625000000000000 : ℝ)^8269 := by
      have hnat : (13118327215584867769 : ℕ)^2048*625000000000000^8269 ≤ 632586890257757^8269*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13118327215584867769 12500000000000000000 632586890257757 625000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632586890257757/625000000000000 : ℝ)) (X := (13118327215584867769/12500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7586890257757/500000000000000 : ℝ)*(0 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7586890257757/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(618327215584867769/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7586890257757/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (1 : ℝ)+(7586890257757/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257586890257757/1250000000000000 : ℝ) by norm_num, show 1+(618327215584867769/25000000000000000000 : ℝ)+(0 : ℝ)=(25618327215584867769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(618327215584867769/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7586890257757/500000000000000 : ℝ)*(2/5 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7586890257757/500000000000000 : ℝ)*(2/5 : ℝ)=(632586890257757/625000000000000 : ℝ) by norm_num, show 1+2*(618327215584867769/25000000000000000000 : ℝ)=(13118327215584867769/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7586890257757/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7586890257757/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7586890257757/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7586890257757/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7586890257757/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7586890257757/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-95627737/500000000 : ℝ)*X 0 0+(6069475693/10000000000 : ℝ)*X 0 1+(2386098479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520454007/10000000000 : ℝ)*X 1 0+(-2658948629/10000000000 : ℝ)*X 1 1+(29826231/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760227003/5000000000 : ℝ)*X 2 0+(1193049241/2500000000 : ℝ)*X 2 1+(-21271589/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((131446887/312500000 : ℝ)*X 0 0+(390535577/1250000000 : ℝ)*X 0 1+(709040443/1250000000 : ℝ)*X 0 2+(131446887/312500000 : ℝ)*X 1 0+(390535577/1250000000 : ℝ)*X 1 1+(709040443/1250000000 : ℝ)*X 1 2+(131446887/312500000 : ℝ)*X 2 0+(390535577/1250000000 : ℝ)*X 2 1+(709040443/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-479473701/2500000000 : ℝ)*X 0 0+(4805689611/10000000000 : ℝ)*X 0 1+(754351297/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584146069/5000000000 : ℝ)*X 1 0+(-698169339/5000000000 : ℝ)*X 1 1+(6034808377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584146017/5000000000 : ℝ)*X 2 0+(6034809913/10000000000 : ℝ)*X 2 1+(-27926727/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105419681/250000000 : ℝ)*X 0 0+(1121307337/2000000000 : ℝ)*X 0 1+(638474863/2000000000 : ℝ)*X 0 2+(105419681/250000000 : ℝ)*X 1 0+(1121307337/2000000000 : ℝ)*X 1 1+(638474863/2000000000 : ℝ)*X 1 2+(105419681/250000000 : ℝ)*X 2 0+(1121307337/2000000000 : ℝ)*X 2 1+(638474863/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (773500125420664197/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (20848161/50000000000000 : ℝ)*(base1) + (484580617/50000000000000 : ℝ)*(base19) + (903028429/100000000000000 : ℝ)*(base23) + (6599317/10000000000000 : ℝ)*(base24) + (219132979/100000000000000 : ℝ)*(upper3) + (145413898867759/25000000000000 : ℝ)*(major0) + (145413898867759/25000000000000 : ℝ)*(major1) + (145413898867759/25000000000000 : ℝ)*(major2) + (770847554617107/100000000000000 : ℝ)*(sp0) + (385424332304469/50000000000000 : ℝ)*(sp1) + (770848664748573/100000000000000 : ℝ)*(sp2) + (392459688764177/100000000000000 : ℝ)*(sp3) + (2120849387/100000000000000 : ℝ)*(sp4) + (1697794707/100000000000000 : ℝ)*(sp7) + (392461428255207/100000000000000 : ℝ)*(f.failure) + (192712408442543/25000000000000 : ℝ)*(f.sum) + (21498339956563/6250000000000000000000000000 : ℝ)*base65 + (51432857230937/12500000000000000000000000000 : ℝ)*base68 + (8985458180937/12500000000000000000000000000 : ℝ)*base70 + (58687498218437/12500000000000000000000000000 : ℝ)*base72 + (24090708675313/6250000000000000000000000000 : ℝ)*base73 + (9378313955937/12500000000000000000000000000 : ℝ)*base76 + (57818984118437/12500000000000000000000000000 : ℝ)*base78 + (19355779280937/12500000000000000000000000000 : ℝ)*base80 + (49400142781563/6250000000000000000000000000 : ℝ)*base81 + (126479111/10000000000000000000000 : ℝ)*base89 + (126479111/10000000000000000000000 : ℝ)*base91 + (126479111/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22524024112623494338179/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129406249/25000000000000 : ℝ)*(base19) + (778240829/100000000000000 : ℝ)*(base23) + (48031949/20000000000000 : ℝ)*(base39) + (42611743/100000000000000 : ℝ)*(base45) + (489061/50000000000000 : ℝ)*(upper2) + (11046847/4000000000000 : ℝ)*(upper5) + (613905537669949/100000000000000 : ℝ)*(major0) + (613905537669949/100000000000000 : ℝ)*(major1) + (153476324377551/25000000000000 : ℝ)*(major2) + (61618337/10000000000000 : ℝ)*(sp2) + (203397307679273/25000000000000 : ℝ)*(sp4) + (794520227629/97656250000 : ℝ)*(sp5) + (406794038226319/50000000000000 : ℝ)*(sp6) + (414221484334927/100000000000000 : ℝ)*(sp7) + (414221484334927/100000000000000 : ℝ)*(f.failure) + (813589470876837/100000000000000 : ℝ)*(f.sum) + (182480625096821/50000000000000000000000000000 : ℝ)*base65 + (92888621825607/12500000000000000000000000000 : ℝ)*base67 + (182324473194393/50000000000000000000000000000 : ℝ)*base69 + (51265565313107/12500000000000000000000000000 : ℝ)*base71 + (166867305346821/50000000000000000000000000000 : ℝ)*base73 + (392767393194393/50000000000000000000000000000 : ℝ)*base75 + (441006933444393/50000000000000000000000000000 : ℝ)*base77 + (93492494594393/50000000000000000000000000000 : ℝ)*base79 + (111290741669393/25000000000000000000000000000 : ℝ)*base81 + (17661329/10000000000000000000000 : ℝ)*base90 + (17661329/10000000000000000000000 : ℝ)*base92 + (17661329/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1077_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1077_s1_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16975217/80000000 : ℝ)*x 0 + (5719238229/10000000000 : ℝ)*x 1 + (77943359/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16975217/80000000 : ℝ)^4135 ≤ (6369185455387/50000000000000 : ℝ)^3111 := by
    have hnat : (16975217 : ℕ)^4135*50000000000000^3111 ≤ 6369185455387^3111*80000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16975217 80000000 6369185455387 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5719238229/10000000000 : ℝ)^4135 ≤ (4758443663549/10000000000000 : ℝ)^3111 := by
    have hnat : (5719238229 : ℕ)^4135*10000000000000^3111 ≤ 4758443663549^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719238229 10000000000 4758443663549 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77943359/156250000 : ℝ)^4135 ≤ (9919298109159/25000000000000 : ℝ)^3111 := by
    have hnat : (77943359 : ℕ)^4135*25000000000000^3111 ≤ 9919298109159^3111*156250000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77943359 156250000 9919298109159 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16975217/80000000 : ℝ), (5719238229/10000000000 : ℝ), (77943359/156250000 : ℝ)] ![(6369185455387/50000000000000 : ℝ), (4758443663549/10000000000000 : ℝ), (9919298109159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16975217/80000000 : ℝ)|^4135 ≤ (6369185455387/50000000000000 : ℝ)^3111
        have hw : |(-16975217/80000000 : ℝ)|=(16975217/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5719238229/10000000000 : ℝ)|^4135 ≤ (4758443663549/10000000000000 : ℝ)^3111
        have hw : |(5719238229/10000000000 : ℝ)|=(5719238229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(77943359/156250000 : ℝ)|^4135 ≤ (9919298109159/25000000000000 : ℝ)^3111
        have hw : |(77943359/156250000 : ℝ)|=(77943359/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271135129/500000000 : ℝ)*x 0 + (-1258825623/5000000000 : ℝ)*x 1 + (2494187633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271135129/500000000 : ℝ)^4135 ≤ (1108336647797/2500000000000 : ℝ)^3111 := by
    have hnat : (271135129 : ℕ)^4135*2500000000000^3111 ≤ 1108336647797^3111*500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271135129 500000000 1108336647797 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1258825623/5000000000 : ℝ)^4135 ≤ (15989338572653/100000000000000 : ℝ)^3111 := by
    have hnat : (1258825623 : ℕ)^4135*100000000000000^3111 ≤ 15989338572653^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258825623 5000000000 15989338572653 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2494187633/5000000000 : ℝ)^4135 ≤ (39677195502517/100000000000000 : ℝ)^3111 := by
    have hnat : (2494187633 : ℕ)^4135*100000000000000^3111 ≤ 39677195502517^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494187633 5000000000 39677195502517 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271135129/500000000 : ℝ), (-1258825623/5000000000 : ℝ), (2494187633/5000000000 : ℝ)] ![(1108336647797/2500000000000 : ℝ), (15989338572653/100000000000000 : ℝ), (39677195502517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271135129/500000000 : ℝ)|^4135 ≤ (1108336647797/2500000000000 : ℝ)^3111
        have hw : |(271135129/500000000 : ℝ)|=(271135129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1258825623/5000000000 : ℝ)|^4135 ≤ (15989338572653/100000000000000 : ℝ)^3111
        have hw : |(-1258825623/5000000000 : ℝ)|=(1258825623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2494187633/5000000000 : ℝ)|^4135 ≤ (39677195502517/100000000000000 : ℝ)^3111
        have hw : |(2494187633/5000000000 : ℝ)|=(2494187633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422703283/10000000000 : ℝ)*x 0 + (623546813/1250000000 : ℝ)*x 1 + (-503530259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422703283/10000000000 : ℝ)^4135 ≤ (2216673677553/5000000000000 : ℝ)^3111 := by
    have hnat : (5422703283 : ℕ)^4135*5000000000000^3111 ≤ 2216673677553^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422703283 10000000000 2216673677553 5000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623546813/1250000000 : ℝ)^4135 ≤ (793543748933/2000000000000 : ℝ)^3111 := by
    have hnat : (623546813 : ℕ)^4135*2000000000000^3111 ≤ 793543748933^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623546813 1250000000 793543748933 2000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503530259/2000000000 : ℝ)^4135 ≤ (7994669493139/50000000000000 : ℝ)^3111 := by
    have hnat : (503530259 : ℕ)^4135*50000000000000^3111 ≤ 7994669493139^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503530259 2000000000 7994669493139 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422703283/10000000000 : ℝ), (623546813/1250000000 : ℝ), (-503530259/2000000000 : ℝ)] ![(2216673677553/5000000000000 : ℝ), (793543748933/2000000000000 : ℝ), (7994669493139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422703283/10000000000 : ℝ)|^4135 ≤ (2216673677553/5000000000000 : ℝ)^3111
        have hw : |(5422703283/10000000000 : ℝ)|=(5422703283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623546813/1250000000 : ℝ)|^4135 ≤ (793543748933/2000000000000 : ℝ)^3111
        have hw : |(623546813/1250000000 : ℝ)|=(623546813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503530259/2000000000 : ℝ)|^4135 ≤ (7994669493139/50000000000000 : ℝ)^3111
        have hw : |(-503530259/2000000000 : ℝ)|=(503530259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322892589/10000000000 : ℝ)*x 0 + (3664681177/10000000000 : ℝ)*x 1 + (1020039713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322892589/10000000000 : ℝ)^4135 ≤ (16400531683107/50000000000000 : ℝ)^3111 := by
    have hnat : (4322892589 : ℕ)^4135*50000000000000^3111 ≤ 16400531683107^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322892589 10000000000 16400531683107 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3664681177/10000000000 : ℝ)^4135 ≤ (13167602427037/50000000000000 : ℝ)^3111 := by
    have hnat : (3664681177 : ℕ)^4135*50000000000000^3111 ≤ 13167602427037^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3664681177 10000000000 13167602427037 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020039713/2000000000 : ℝ)^4135 ≤ (1021593294209/2500000000000 : ℝ)^3111 := by
    have hnat : (1020039713 : ℕ)^4135*2500000000000^3111 ≤ 1021593294209^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020039713 2000000000 1021593294209 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322892589/10000000000 : ℝ), (3664681177/10000000000 : ℝ), (1020039713/2000000000 : ℝ)] ![(16400531683107/50000000000000 : ℝ), (13167602427037/50000000000000 : ℝ), (1021593294209/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322892589/10000000000 : ℝ)|^4135 ≤ (16400531683107/50000000000000 : ℝ)^3111
        have hw : |(4322892589/10000000000 : ℝ)|=(4322892589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3664681177/10000000000 : ℝ)|^4135 ≤ (13167602427037/50000000000000 : ℝ)^3111
        have hw : |(3664681177/10000000000 : ℝ)|=(3664681177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1020039713/2000000000 : ℝ)|^4135 ≤ (1021593294209/2500000000000 : ℝ)^3111
        have hw : |(1020039713/2000000000 : ℝ)|=(1020039713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061403591/5000000000 : ℝ)*x 0 + (1249650867/2500000000 : ℝ)*x 1 + (356800021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061403591/5000000000 : ℝ)^4135 ≤ (12745593126547/100000000000000 : ℝ)^3111 := by
    have hnat : (1061403591 : ℕ)^4135*100000000000000^3111 ≤ 12745593126547^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061403591 5000000000 12745593126547 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249650867/2500000000 : ℝ)^4135 ≤ (1989268228809/5000000000000 : ℝ)^3111 := by
    have hnat : (1249650867 : ℕ)^4135*5000000000000^3111 ≤ 1989268228809^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249650867 2500000000 1989268228809 5000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356800021/625000000 : ℝ)^4135 ≤ (23734521139457/50000000000000 : ℝ)^3111 := by
    have hnat : (356800021 : ℕ)^4135*50000000000000^3111 ≤ 23734521139457^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356800021 625000000 23734521139457 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061403591/5000000000 : ℝ), (1249650867/2500000000 : ℝ), (356800021/625000000 : ℝ)] ![(12745593126547/100000000000000 : ℝ), (1989268228809/5000000000000 : ℝ), (23734521139457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061403591/5000000000 : ℝ)|^4135 ≤ (12745593126547/100000000000000 : ℝ)^3111
        have hw : |(-1061403591/5000000000 : ℝ)|=(1061403591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249650867/2500000000 : ℝ)|^4135 ≤ (1989268228809/5000000000000 : ℝ)^3111
        have hw : |(1249650867/2500000000 : ℝ)|=(1249650867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356800021/625000000 : ℝ)|^4135 ≤ (23734521139457/50000000000000 : ℝ)^3111
        have hw : |(356800021/625000000 : ℝ)|=(356800021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (327246503/625000000 : ℝ)*x 0 + (-1797223617/10000000000 : ℝ)*x 1 + (5708802363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327246503/625000000 : ℝ)^4135 ≤ (4231563905769/10000000000000 : ℝ)^3111 := by
    have hnat : (327246503 : ℕ)^4135*10000000000000^3111 ≤ 4231563905769^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327246503 625000000 4231563905769 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797223617/10000000000 : ℝ)^4135 ≤ (10215296238351/100000000000000 : ℝ)^3111 := by
    have hnat : (1797223617 : ℕ)^4135*100000000000000^3111 ≤ 10215296238351^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797223617 10000000000 10215296238351 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5708802363/10000000000 : ℝ)^4135 ≤ (11867266170333/25000000000000 : ℝ)^3111 := by
    have hnat : (5708802363 : ℕ)^4135*25000000000000^3111 ≤ 11867266170333^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708802363 10000000000 11867266170333 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327246503/625000000 : ℝ), (-1797223617/10000000000 : ℝ), (5708802363/10000000000 : ℝ)] ![(4231563905769/10000000000000 : ℝ), (10215296238351/100000000000000 : ℝ), (11867266170333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327246503/625000000 : ℝ)|^4135 ≤ (4231563905769/10000000000000 : ℝ)^3111
        have hw : |(327246503/625000000 : ℝ)|=(327246503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797223617/10000000000 : ℝ)|^4135 ≤ (10215296238351/100000000000000 : ℝ)^3111
        have hw : |(-1797223617/10000000000 : ℝ)|=(1797223617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5708802363/10000000000 : ℝ)|^4135 ≤ (11867266170333/25000000000000 : ℝ)^3111
        have hw : |(5708802363/10000000000 : ℝ)|=(5708802363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1308985493/2500000000 : ℝ)*x 0 + (89200073/156250000 : ℝ)*x 1 + (-224652899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308985493/2500000000 : ℝ)^4135 ≤ (42315616757491/100000000000000 : ℝ)^3111 := by
    have hnat : (1308985493 : ℕ)^4135*100000000000000^3111 ≤ 42315616757491^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308985493 2500000000 42315616757491 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89200073/156250000 : ℝ)^4135 ≤ (47469090200419/100000000000000 : ℝ)^3111 := by
    have hnat : (89200073 : ℕ)^4135*100000000000000^3111 ≤ 47469090200419^3111*156250000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89200073 156250000 47469090200419 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224652899/1250000000 : ℝ)^4135 ≤ (10215293027551/100000000000000 : ℝ)^3111 := by
    have hnat : (224652899 : ℕ)^4135*100000000000000^3111 ≤ 10215293027551^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224652899 1250000000 10215293027551 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308985493/2500000000 : ℝ), (89200073/156250000 : ℝ), (-224652899/1250000000 : ℝ)] ![(42315616757491/100000000000000 : ℝ), (47469090200419/100000000000000 : ℝ), (10215293027551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308985493/2500000000 : ℝ)|^4135 ≤ (42315616757491/100000000000000 : ℝ)^3111
        have hw : |(1308985493/2500000000 : ℝ)|=(1308985493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89200073/156250000 : ℝ)|^4135 ≤ (47469090200419/100000000000000 : ℝ)^3111
        have hw : |(89200073/156250000 : ℝ)|=(89200073/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224652899/1250000000 : ℝ)|^4135 ≤ (10215293027551/100000000000000 : ℝ)^3111
        have hw : |(-224652899/1250000000 : ℝ)|=(224652899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324665683/10000000000 : ℝ)*x 0 + (2540052483/5000000000 : ℝ)*x 1 + (3685178601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324665683/10000000000 : ℝ)^4135 ≤ (8204736691179/25000000000000 : ℝ)^3111 := by
    have hnat : (4324665683 : ℕ)^4135*25000000000000^3111 ≤ 8204736691179^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324665683 10000000000 8204736691179 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540052483/5000000000 : ℝ)^4135 ≤ (20324942611453/50000000000000 : ℝ)^3111 := by
    have hnat : (2540052483 : ℕ)^4135*50000000000000^3111 ≤ 20324942611453^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540052483 5000000000 20324942611453 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685178601/10000000000 : ℝ)^4135 ≤ (13265583996051/50000000000000 : ℝ)^3111 := by
    have hnat : (3685178601 : ℕ)^4135*50000000000000^3111 ≤ 13265583996051^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685178601 10000000000 13265583996051 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324665683/10000000000 : ℝ), (2540052483/5000000000 : ℝ), (3685178601/10000000000 : ℝ)] ![(8204736691179/25000000000000 : ℝ), (20324942611453/50000000000000 : ℝ), (13265583996051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324665683/10000000000 : ℝ)|^4135 ≤ (8204736691179/25000000000000 : ℝ)^3111
        have hw : |(4324665683/10000000000 : ℝ)|=(4324665683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540052483/5000000000 : ℝ)|^4135 ≤ (20324942611453/50000000000000 : ℝ)^3111
        have hw : |(2540052483/5000000000 : ℝ)|=(2540052483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685178601/10000000000 : ℝ)|^4135 ≤ (13265583996051/50000000000000 : ℝ)^3111
        have hw : |(3685178601/10000000000 : ℝ)|=(3685178601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_8 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (414737/500000000 : ℝ)*x 0 + (1097978597/2000000000 : ℝ)*x 1 + (6371258317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414737/500000000 : ℝ)^4135 ≤ (802809493/10000000000000 : ℝ)^3111 := by
    have hnat : (414737 : ℕ)^4135*10000000000000^3111 ≤ 802809493^3111*500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414737 500000000 802809493 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097978597/2000000000 : ℝ)^4135 ≤ (5633134764207/12500000000000 : ℝ)^3111 := by
    have hnat : (1097978597 : ℕ)^4135*12500000000000^3111 ≤ 5633134764207^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097978597 2000000000 5633134764207 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6371258317/10000000000 : ℝ)^4135 ≤ (3432930861017/6250000000000 : ℝ)^3111 := by
    have hnat : (6371258317 : ℕ)^4135*6250000000000^3111 ≤ 3432930861017^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6371258317 10000000000 3432930861017 6250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414737/500000000 : ℝ), (1097978597/2000000000 : ℝ), (6371258317/10000000000 : ℝ)] ![(802809493/10000000000000 : ℝ), (5633134764207/12500000000000 : ℝ), (3432930861017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414737/500000000 : ℝ)|^4135 ≤ (802809493/10000000000000 : ℝ)^3111
        have hw : |(414737/500000000 : ℝ)|=(414737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097978597/2000000000 : ℝ)|^4135 ≤ (5633134764207/12500000000000 : ℝ)^3111
        have hw : |(1097978597/2000000000 : ℝ)|=(1097978597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6371258317/10000000000 : ℝ)|^4135 ≤ (3432930861017/6250000000000 : ℝ)^3111
        have hw : |(6371258317/10000000000 : ℝ)|=(6371258317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_9 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (966251769/10000000000 : ℝ)*x 0 + (-2225898783/5000000000 : ℝ)*x 1 + (6929586213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966251769/10000000000 : ℝ)^4135 ≤ (447742266647/10000000000000 : ℝ)^3111 := by
    have hnat : (966251769 : ℕ)^4135*10000000000000^3111 ≤ 447742266647^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966251769 10000000000 447742266647 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225898783/5000000000 : ℝ)^4135 ≤ (34107447235297/100000000000000 : ℝ)^3111 := by
    have hnat : (2225898783 : ℕ)^4135*100000000000000^3111 ≤ 34107447235297^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225898783 5000000000 34107447235297 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6929586213/10000000000 : ℝ)^4135 ≤ (3070756504537/5000000000000 : ℝ)^3111 := by
    have hnat : (6929586213 : ℕ)^4135*5000000000000^3111 ≤ 3070756504537^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6929586213 10000000000 3070756504537 5000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(966251769/10000000000 : ℝ), (-2225898783/5000000000 : ℝ), (6929586213/10000000000 : ℝ)] ![(447742266647/10000000000000 : ℝ), (34107447235297/100000000000000 : ℝ), (3070756504537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(966251769/10000000000 : ℝ)|^4135 ≤ (447742266647/10000000000000 : ℝ)^3111
        have hw : |(966251769/10000000000 : ℝ)|=(966251769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225898783/5000000000 : ℝ)|^4135 ≤ (34107447235297/100000000000000 : ℝ)^3111
        have hw : |(-2225898783/5000000000 : ℝ)|=(2225898783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6929586213/10000000000 : ℝ)|^4135 ≤ (3070756504537/5000000000000 : ℝ)^3111
        have hw : |(6929586213/10000000000 : ℝ)|=(6929586213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_10 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (966245231/10000000000 : ℝ)*x 0 + (6929571997/10000000000 : ℝ)*x 1 + (-1112954491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966245231/10000000000 : ℝ)^4135 ≤ (2238691199343/50000000000000 : ℝ)^3111 := by
    have hnat : (966245231 : ℕ)^4135*50000000000000^3111 ≤ 2238691199343^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966245231 10000000000 2238691199343 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6929571997/10000000000 : ℝ)^4135 ≤ (30707481313489/50000000000000 : ℝ)^3111 := by
    have hnat : (6929571997 : ℕ)^4135*50000000000000^3111 ≤ 30707481313489^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6929571997 10000000000 30707481313489 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112954491/2500000000 : ℝ)^4135 ≤ (4263456869347/12500000000000 : ℝ)^3111 := by
    have hnat : (1112954491 : ℕ)^4135*12500000000000^3111 ≤ 4263456869347^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112954491 2500000000 4263456869347 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(966245231/10000000000 : ℝ), (6929571997/10000000000 : ℝ), (-1112954491/2500000000 : ℝ)] ![(2238691199343/50000000000000 : ℝ), (30707481313489/50000000000000 : ℝ), (4263456869347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(966245231/10000000000 : ℝ)|^4135 ≤ (2238691199343/50000000000000 : ℝ)^3111
        have hw : |(966245231/10000000000 : ℝ)|=(966245231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6929571997/10000000000 : ℝ)|^4135 ≤ (30707481313489/50000000000000 : ℝ)^3111
        have hw : |(6929571997/10000000000 : ℝ)|=(6929571997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112954491/2500000000 : ℝ)|^4135 ≤ (4263456869347/12500000000000 : ℝ)^3111
        have hw : |(-1112954491/2500000000 : ℝ)|=(1112954491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s1_11 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (384746371/2000000000 : ℝ)*x 0 + (5827812181/10000000000 : ℝ)*x 1 + (5021634699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384746371/2000000000 : ℝ)^4135 ≤ (1397743308177/12500000000000 : ℝ)^3111 := by
    have hnat : (384746371 : ℕ)^4135*12500000000000^3111 ≤ 1397743308177^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384746371 2000000000 1397743308177 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5827812181/10000000000 : ℝ)^4135 ≤ (24394426936217/50000000000000 : ℝ)^3111 := by
    have hnat : (5827812181 : ℕ)^4135*50000000000000^3111 ≤ 24394426936217^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5827812181 10000000000 24394426936217 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021634699/10000000000 : ℝ)^4135 ≤ (40029199646943/100000000000000 : ℝ)^3111 := by
    have hnat : (5021634699 : ℕ)^4135*100000000000000^3111 ≤ 40029199646943^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021634699 10000000000 40029199646943 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(384746371/2000000000 : ℝ), (5827812181/10000000000 : ℝ), (5021634699/10000000000 : ℝ)] ![(1397743308177/12500000000000 : ℝ), (24394426936217/50000000000000 : ℝ), (40029199646943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(384746371/2000000000 : ℝ)|^4135 ≤ (1397743308177/12500000000000 : ℝ)^3111
        have hw : |(384746371/2000000000 : ℝ)|=(384746371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5827812181/10000000000 : ℝ)|^4135 ≤ (24394426936217/50000000000000 : ℝ)^3111
        have hw : |(5827812181/10000000000 : ℝ)|=(5827812181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021634699/10000000000 : ℝ)|^4135 ≤ (40029199646943/100000000000000 : ℝ)^3111
        have hw : |(5021634699/10000000000 : ℝ)|=(5021634699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2639/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (143/100000 : ℝ) ^ (8269/2048 : ℝ) ≤ (10215073/3125000000000000000 : ℝ) := by
    have hpowers : (143/100000 : ℝ)^8269 ≤ (10215073/3125000000000000000 : ℝ)^2048 := by
      have hnat : (143 : ℕ)^8269*3125000000000000000^2048 ≤ 10215073^2048*100000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143 100000 10215073 3125000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (143/100000 : ℝ)) (X := (10215073/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/50000 : ℝ) ^ (8269/2048 : ℝ) ≤ (591527533652717743/100000000000000000000 : ℝ) := by
    have hpowers : (14033/50000 : ℝ)^8269 ≤ (591527533652717743/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14033 : ℕ)^8269*100000000000000000000^2048 ≤ 591527533652717743^2048*50000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 50000 591527533652717743 100000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/50000 : ℝ)) (X := (591527533652717743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500000010215073/1562500000000000000 : ℝ) ≤ (156250000000253/156250000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (1562500000010215073/1562500000000000000 : ℝ)^2048 ≤ (156250000000253/156250000000000 : ℝ)^8269 := by
      have hnat : (1562500000010215073 : ℕ)^2048*156250000000000^8269 ≤ 156250000000253^8269*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500000010215073 1562500000000000000 156250000000253 156250000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250000000253/156250000000000 : ℝ)) (X := (1562500000010215073/1562500000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100591527533979600079/100000000000000000000 : ℝ) ≤ (2503654498897711/2500000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (100591527533979600079/100000000000000000000 : ℝ)^2048 ≤ (2503654498897711/2500000000000000 : ℝ)^8269 := by
      have hnat : (100591527533979600079 : ℕ)^2048*2500000000000000^8269 ≤ 2503654498897711^8269*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100591527533979600079 100000000000000000000 2503654498897711 2500000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503654498897711/2500000000000000 : ℝ)) (X := (100591527533979600079/100000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50591527533652717743/50000000000000000000 : ℝ) ≤ (1253654498895687/1250000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (50591527533652717743/50000000000000000000 : ℝ)^2048 ≤ (1253654498895687/1250000000000000 : ℝ)^8269 := by
      have hnat : (50591527533652717743 : ℕ)^2048*1250000000000000^8269 ≤ 1253654498895687^8269*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50591527533652717743 50000000000000000000 1253654498895687 1250000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253654498895687/1250000000000000 : ℝ)) (X := (50591527533652717743/50000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10215073/3125000000000000000 : ℝ) ≤ ((34903227406714722343/34903750000000000000 : ℝ)+2*(3654498893663/698075000000000 : ℝ)*(143/100000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (34903227406714722343/34903750000000000000 : ℝ)+2*(3654498893663/698075000000000 : ℝ)*(143/100000 : ℝ)=(156250000000253/156250000000000 : ℝ) by norm_num, show 1+2*(10215073/3125000000000000000 : ℝ)=(1562500000010215073/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(591527533652717743/100000000000000000000 : ℝ)+(10215073/3125000000000000000 : ℝ) ≤ ((34903227406714722343/34903750000000000000 : ℝ)+(3654498893663/698075000000000 : ℝ)*((14033/50000 : ℝ)+(143/100000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (34903227406714722343/34903750000000000000 : ℝ)+(3654498893663/698075000000000 : ℝ)*((14033/50000 : ℝ)+(143/100000 : ℝ))=(2503654498897711/2500000000000000 : ℝ) by norm_num, show 1+(591527533652717743/100000000000000000000 : ℝ)+(10215073/3125000000000000000 : ℝ)=(100591527533979600079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(591527533652717743/100000000000000000000 : ℝ) ≤ ((34903227406714722343/34903750000000000000 : ℝ)+2*(3654498893663/698075000000000 : ℝ)*(14033/50000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (34903227406714722343/34903750000000000000 : ℝ)+2*(3654498893663/698075000000000 : ℝ)*(14033/50000 : ℝ)=(1253654498895687/1250000000000000 : ℝ) by norm_num, show 1+2*(591527533652717743/100000000000000000000 : ℝ)=(50591527533652717743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34903227406714722343/34903750000000000000 : ℝ)*(X 1 0+X 2 0)+(3654498893663/698075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (143/100000 : ℝ)) (hi := (14033/50000 : ℝ)) (c := (34903227406714722343/34903750000000000000 : ℝ)) (alpha := (3654498893663/698075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34903227406714722343/34903750000000000000 : ℝ)*(X 0 1+X 2 1)+(3654498893663/698075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (143/100000 : ℝ)) (hi := (14033/50000 : ℝ)) (c := (34903227406714722343/34903750000000000000 : ℝ)) (alpha := (3654498893663/698075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34903227406714722343/34903750000000000000 : ℝ)*(X 0 2+X 1 2)+(3654498893663/698075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (143/100000 : ℝ)) (hi := (14033/50000 : ℝ)) (c := (34903227406714722343/34903750000000000000 : ℝ)) (alpha := (3654498893663/698075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16975217/80000000 : ℝ)*X 0 0+(5719238229/10000000000 : ℝ)*X 0 1+(77943359/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((271135129/500000000 : ℝ)*X 1 0+(-1258825623/5000000000 : ℝ)*X 1 1+(2494187633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5422703283/10000000000 : ℝ)*X 2 0+(623546813/1250000000 : ℝ)*X 2 1+(-503530259/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322892589/10000000000 : ℝ)*X 0 0+(3664681177/10000000000 : ℝ)*X 0 1+(1020039713/2000000000 : ℝ)*X 0 2+(4322892589/10000000000 : ℝ)*X 1 0+(3664681177/10000000000 : ℝ)*X 1 1+(1020039713/2000000000 : ℝ)*X 1 2+(4322892589/10000000000 : ℝ)*X 2 0+(3664681177/10000000000 : ℝ)*X 2 1+(1020039713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061403591/5000000000 : ℝ)*X 0 0+(1249650867/2500000000 : ℝ)*X 0 1+(356800021/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327246503/625000000 : ℝ)*X 1 0+(-1797223617/10000000000 : ℝ)*X 1 1+(5708802363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1308985493/2500000000 : ℝ)*X 2 0+(89200073/156250000 : ℝ)*X 2 1+(-224652899/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324665683/10000000000 : ℝ)*X 0 0+(2540052483/5000000000 : ℝ)*X 0 1+(3685178601/10000000000 : ℝ)*X 0 2+(4324665683/10000000000 : ℝ)*X 1 0+(2540052483/5000000000 : ℝ)*X 1 1+(3685178601/10000000000 : ℝ)*X 1 2+(4324665683/10000000000 : ℝ)*X 2 0+(2540052483/5000000000 : ℝ)*X 2 1+(3685178601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((414737/500000000 : ℝ)*X 0 0+(1097978597/2000000000 : ℝ)*X 0 1+(6371258317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((966251769/10000000000 : ℝ)*X 1 0+(-2225898783/5000000000 : ℝ)*X 1 1+(6929586213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((966245231/10000000000 : ℝ)*X 2 0+(6929571997/10000000000 : ℝ)*X 2 1+(-1112954491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((384746371/2000000000 : ℝ)*X 0 0+(5827812181/10000000000 : ℝ)*X 0 1+(5021634699/10000000000 : ℝ)*X 0 2+(384746371/2000000000 : ℝ)*X 1 0+(5827812181/10000000000 : ℝ)*X 1 1+(5021634699/10000000000 : ℝ)*X 1 2+(384746371/2000000000 : ℝ)*X 2 0+(5827812181/10000000000 : ℝ)*X 2 1+(5021634699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1526551849958305858199736663/218148437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (64526975220563/6250000000000 : ℝ)*(major0) + (64526975220563/6250000000000 : ℝ)*(major1) + (64526975220563/6250000000000 : ℝ)*(major2) + (1368246813974207/100000000000000 : ℝ)*(sp0) + (1368247502491611/100000000000000 : ℝ)*(sp1) + (684123274824207/50000000000000 : ℝ)*(sp2) + (87076670102173/12500000000000 : ℝ)*(sp3) + (26387771/2000000000000 : ℝ)*(sp4) + (815455697/100000000000000 : ℝ)*(sp5) + (792349079/50000000000000 : ℝ)*(sp6) + (581325393/100000000000000 : ℝ)*(sp8) + (396740841/100000000000000 : ℝ)*(sp9) + (580341577/100000000000000 : ℝ)*(sp10) + (224573397/25000000000000 : ℝ)*(sp11) + (174153564777743/25000000000000 : ℝ)*(f.failure) + (1368248714688149/100000000000000 : ℝ)*(f.sum) + (350673474523201/139615000000000000000000000000 : ℝ)*base65 + (433764891861401609/218148437500000000000000000000000 : ℝ)*base67 + (1367303892023381343/436296875000000000000000000000000 : ℝ)*base69 + (3013755622138881343/436296875000000000000000000000000 : ℝ)*base71 + (251318520731309/139615000000000000000000000000 : ℝ)*base74 + (1032201395872208617/109074218750000000000000000000000 : ℝ)*base75 + (3589491032504818843/436296875000000000000000000000000 : ℝ)*base77 + (4122770788376881343/436296875000000000000000000000000 : ℝ)*base79 + (51049579788877/69807500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (14423761/2500000000000000000000 : ℝ)*base90 + (14423761/2500000000000000000000 : ℝ)*base92 + (14423761/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (204292663338737422366431/69807500000000000000000000000 : ℝ) := by norm_num
    linear_combination (245404911/100000000000000 : ℝ)*(lower4) + (15791867/50000000000000 : ℝ)*(upper5) + (1062471394054247/100000000000000 : ℝ)*(major0) + (1062471394054247/100000000000000 : ℝ)*(major1) + (1062471394054247/100000000000000 : ℝ)*(major2) + (884048609/100000000000000 : ℝ)*(sp0) + (398095943/25000000000000 : ℝ)*(sp1) + (1026007401/25000000000000 : ℝ)*(sp2) + (1408055212477611/100000000000000 : ℝ)*(sp4) + (1408058042225717/100000000000000 : ℝ)*(sp5) + (281611106115977/20000000000000 : ℝ)*(sp6) + (358441016519063/50000000000000 : ℝ)*(sp7) + (3538083269/100000000000000 : ℝ)*(sp8) + (102291039/10000000000000 : ℝ)*(sp11) + (143376611189703/20000000000000 : ℝ)*(f.failure) + (1408059634609489/100000000000000 : ℝ)*(f.sum) + (259026473119829/139615000000000000000000000000 : ℝ)*base65 + (9257126666817990721/3490375000000000000000000000000000 : ℝ)*base67 + (3125877797695384279/3490375000000000000000000000000000 : ℝ)*base70 + (14970427250231490721/3490375000000000000000000000000000 : ℝ)*base71 + (219105165991031/139615000000000000000000000000 : ℝ)*base74 + (1681800306746634279/3490375000000000000000000000000000 : ℝ)*base76 + (7510766470625490721/3490375000000000000000000000000000 : ℝ)*base77 + (3584112213597759279/3490375000000000000000000000000000 : ℝ)*base80 + (259285155377/68171386718750000000000000 : ℝ)*base82 + (10630681/2000000000000000000000 : ℝ)*base90 + (10630681/2000000000000000000000 : ℝ)*base92 + (10630681/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1077_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1077_s2_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178704201/10000000000 : ℝ)*x 0 + (690453353/1250000000 : ℝ)*x 1 + (2573968251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178704201/10000000000 : ℝ)^4135 ≤ (13193595925131/100000000000000 : ℝ)^3111 := by
    have hnat : (2178704201 : ℕ)^4135*100000000000000^3111 ≤ 13193595925131^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178704201 10000000000 13193595925131 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690453353/1250000000 : ℝ)^4135 ≤ (2839594305059/6250000000000 : ℝ)^3111 := by
    have hnat : (690453353 : ℕ)^4135*6250000000000^3111 ≤ 2839594305059^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690453353 1250000000 2839594305059 6250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573968251/5000000000 : ℝ)^4135 ≤ (41372895182259/100000000000000 : ℝ)^3111 := by
    have hnat : (2573968251 : ℕ)^4135*100000000000000^3111 ≤ 41372895182259^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573968251 5000000000 41372895182259 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178704201/10000000000 : ℝ), (690453353/1250000000 : ℝ), (2573968251/5000000000 : ℝ)] ![(13193595925131/100000000000000 : ℝ), (2839594305059/6250000000000 : ℝ), (41372895182259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178704201/10000000000 : ℝ)|^4135 ≤ (13193595925131/100000000000000 : ℝ)^3111
        have hw : |(-2178704201/10000000000 : ℝ)|=(2178704201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690453353/1250000000 : ℝ)|^4135 ≤ (2839594305059/6250000000000 : ℝ)^3111
        have hw : |(690453353/1250000000 : ℝ)|=(690453353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573968251/5000000000 : ℝ)|^4135 ≤ (41372895182259/100000000000000 : ℝ)^3111
        have hw : |(2573968251/5000000000 : ℝ)|=(2573968251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376707423/10000000000 : ℝ)*x 0 + (-474908101/2000000000 : ℝ)*x 1 + (16087303/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376707423/10000000000 : ℝ)^4135 ≤ (21917178295351/50000000000000 : ℝ)^3111 := by
    have hnat : (5376707423 : ℕ)^4135*50000000000000^3111 ≤ 21917178295351^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376707423 10000000000 21917178295351 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474908101/2000000000 : ℝ)^4135 ≤ (14792743316009/100000000000000 : ℝ)^3111 := by
    have hnat : (474908101 : ℕ)^4135*100000000000000^3111 ≤ 14792743316009^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474908101 2000000000 14792743316009 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16087303/31250000 : ℝ)^4135 ≤ (41372900074679/100000000000000 : ℝ)^3111 := by
    have hnat : (16087303 : ℕ)^4135*100000000000000^3111 ≤ 41372900074679^3111*31250000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16087303 31250000 41372900074679 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376707423/10000000000 : ℝ), (-474908101/2000000000 : ℝ), (16087303/31250000 : ℝ)] ![(21917178295351/50000000000000 : ℝ), (14792743316009/100000000000000 : ℝ), (41372900074679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376707423/10000000000 : ℝ)|^4135 ≤ (21917178295351/50000000000000 : ℝ)^3111
        have hw : |(5376707423/10000000000 : ℝ)|=(5376707423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474908101/2000000000 : ℝ)|^4135 ≤ (14792743316009/100000000000000 : ℝ)^3111
        have hw : |(-474908101/2000000000 : ℝ)|=(474908101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16087303/31250000 : ℝ)|^4135 ≤ (41372900074679/100000000000000 : ℝ)^3111
        have hw : |(16087303/31250000 : ℝ)|=(16087303/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344176899/2500000000 : ℝ)*x 0 + (2573968389/5000000000 : ℝ)*x 1 + (-1187270257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344176899/2500000000 : ℝ)^4135 ≤ (876687169307/2000000000000 : ℝ)^3111 := by
    have hnat : (1344176899 : ℕ)^4135*2000000000000^3111 ≤ 876687169307^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344176899 2500000000 876687169307 2000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573968389/5000000000 : ℝ)^4135 ≤ (41372898130529/100000000000000 : ℝ)^3111 := by
    have hnat : (2573968389 : ℕ)^4135*100000000000000^3111 ≤ 41372898130529^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573968389 5000000000 41372898130529 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187270257/5000000000 : ℝ)^4135 ≤ (3698185847633/25000000000000 : ℝ)^3111 := by
    have hnat : (1187270257 : ℕ)^4135*25000000000000^3111 ≤ 3698185847633^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187270257 5000000000 3698185847633 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344176899/2500000000 : ℝ), (2573968389/5000000000 : ℝ), (-1187270257/5000000000 : ℝ)] ![(876687169307/2000000000000 : ℝ), (41372898130529/100000000000000 : ℝ), (3698185847633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344176899/2500000000 : ℝ)|^4135 ≤ (876687169307/2000000000000 : ℝ)^3111
        have hw : |(1344176899/2500000000 : ℝ)|=(1344176899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573968389/5000000000 : ℝ)|^4135 ≤ (41372898130529/100000000000000 : ℝ)^3111
        have hw : |(2573968389/5000000000 : ℝ)|=(2573968389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187270257/5000000000 : ℝ)|^4135 ≤ (3698185847633/25000000000000 : ℝ)^3111
        have hw : |(-1187270257/5000000000 : ℝ)|=(1187270257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361682353/10000000000 : ℝ)*x 0 + (4008424987/10000000000 : ℝ)*x 1 + (4746333089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361682353/10000000000 : ℝ)^4135 ≤ (16596423241991/50000000000000 : ℝ)^3111 := by
    have hnat : (4361682353 : ℕ)^4135*50000000000000^3111 ≤ 16596423241991^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361682353 10000000000 16596423241991 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4008424987/10000000000 : ℝ)^4135 ≤ (29668168893577/100000000000000 : ℝ)^3111 := by
    have hnat : (4008424987 : ℕ)^4135*100000000000000^3111 ≤ 29668168893577^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008424987 10000000000 29668168893577 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4746333089/10000000000 : ℝ)^4135 ≤ (1856949230711/5000000000000 : ℝ)^3111 := by
    have hnat : (4746333089 : ℕ)^4135*5000000000000^3111 ≤ 1856949230711^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4746333089 10000000000 1856949230711 5000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361682353/10000000000 : ℝ), (4008424987/10000000000 : ℝ), (4746333089/10000000000 : ℝ)] ![(16596423241991/50000000000000 : ℝ), (29668168893577/100000000000000 : ℝ), (1856949230711/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361682353/10000000000 : ℝ)|^4135 ≤ (16596423241991/50000000000000 : ℝ)^3111
        have hw : |(4361682353/10000000000 : ℝ)|=(4361682353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4008424987/10000000000 : ℝ)|^4135 ≤ (29668168893577/100000000000000 : ℝ)^3111
        have hw : |(4008424987/10000000000 : ℝ)|=(4008424987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4746333089/10000000000 : ℝ)|^4135 ≤ (1856949230711/5000000000000 : ℝ)^3111
        have hw : |(4746333089/10000000000 : ℝ)|=(4746333089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178826457/10000000000 : ℝ)*x 0 + (5150647983/10000000000 : ℝ)*x 1 + (5520887023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178826457/10000000000 : ℝ)^4135 ≤ (6597289984663/50000000000000 : ℝ)^3111 := by
    have hnat : (2178826457 : ℕ)^4135*50000000000000^3111 ≤ 6597289984663^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178826457 10000000000 6597289984663 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150647983/10000000000 : ℝ)^4135 ≤ (41401862110307/100000000000000 : ℝ)^3111 := by
    have hnat : (5150647983 : ℕ)^4135*100000000000000^3111 ≤ 41401862110307^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150647983 10000000000 41401862110307 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520887023/10000000000 : ℝ)^4135 ≤ (11350889475639/25000000000000 : ℝ)^3111 := by
    have hnat : (5520887023 : ℕ)^4135*25000000000000^3111 ≤ 11350889475639^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520887023 10000000000 11350889475639 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178826457/10000000000 : ℝ), (5150647983/10000000000 : ℝ), (5520887023/10000000000 : ℝ)] ![(6597289984663/50000000000000 : ℝ), (41401862110307/100000000000000 : ℝ), (11350889475639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178826457/10000000000 : ℝ)|^4135 ≤ (6597289984663/50000000000000 : ℝ)^3111
        have hw : |(-2178826457/10000000000 : ℝ)|=(2178826457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150647983/10000000000 : ℝ)|^4135 ≤ (41401862110307/100000000000000 : ℝ)^3111
        have hw : |(5150647983/10000000000 : ℝ)|=(5150647983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520887023/10000000000 : ℝ)|^4135 ≤ (11350889475639/25000000000000 : ℝ)^3111
        have hw : |(5520887023/10000000000 : ℝ)|=(5520887023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5281806437/10000000000 : ℝ)*x 0 + (-250198797/1250000000 : ℝ)*x 1 + (5520887117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281806437/10000000000 : ℝ)^4135 ≤ (1070224934899/2500000000000 : ℝ)^3111 := by
    have hnat : (5281806437 : ℕ)^4135*2500000000000^3111 ≤ 1070224934899^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281806437 10000000000 1070224934899 2500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250198797/1250000000 : ℝ)^4135 ≤ (2946860916069/25000000000000 : ℝ)^3111 := by
    have hnat : (250198797 : ℕ)^4135*25000000000000^3111 ≤ 2946860916069^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250198797 1250000000 2946860916069 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520887117/10000000000 : ℝ)^4135 ≤ (22701779465031/50000000000000 : ℝ)^3111 := by
    have hnat : (5520887117 : ℕ)^4135*50000000000000^3111 ≤ 22701779465031^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520887117 10000000000 22701779465031 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281806437/10000000000 : ℝ), (-250198797/1250000000 : ℝ), (5520887117/10000000000 : ℝ)] ![(1070224934899/2500000000000 : ℝ), (2946860916069/25000000000000 : ℝ), (22701779465031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281806437/10000000000 : ℝ)|^4135 ≤ (1070224934899/2500000000000 : ℝ)^3111
        have hw : |(5281806437/10000000000 : ℝ)|=(5281806437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250198797/1250000000 : ℝ)|^4135 ≤ (2946860916069/25000000000000 : ℝ)^3111
        have hw : |(-250198797/1250000000 : ℝ)|=(250198797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520887117/10000000000 : ℝ)|^4135 ≤ (22701779465031/50000000000000 : ℝ)^3111
        have hw : |(5520887117/10000000000 : ℝ)|=(5520887117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640903339/5000000000 : ℝ)*x 0 + (2760443479/5000000000 : ℝ)*x 1 + (-400318053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640903339/5000000000 : ℝ)^4135 ≤ (21404499996101/50000000000000 : ℝ)^3111 := by
    have hnat : (2640903339 : ℕ)^4135*50000000000000^3111 ≤ 21404499996101^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640903339 5000000000 21404499996101 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760443479/5000000000 : ℝ)^4135 ≤ (45403557192047/100000000000000 : ℝ)^3111 := by
    have hnat : (2760443479 : ℕ)^4135*100000000000000^3111 ≤ 45403557192047^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760443479 5000000000 45403557192047 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400318053/2000000000 : ℝ)^4135 ≤ (1178744279543/10000000000000 : ℝ)^3111 := by
    have hnat : (400318053 : ℕ)^4135*10000000000000^3111 ≤ 1178744279543^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400318053 2000000000 1178744279543 10000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640903339/5000000000 : ℝ), (2760443479/5000000000 : ℝ), (-400318053/2000000000 : ℝ)] ![(21404499996101/50000000000000 : ℝ), (45403557192047/100000000000000 : ℝ), (1178744279543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640903339/5000000000 : ℝ)|^4135 ≤ (21404499996101/50000000000000 : ℝ)^3111
        have hw : |(2640903339/5000000000 : ℝ)|=(2640903339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760443479/5000000000 : ℝ)|^4135 ≤ (45403557192047/100000000000000 : ℝ)^3111
        have hw : |(2760443479/5000000000 : ℝ)|=(2760443479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400318053/2000000000 : ℝ)|^4135 ≤ (1178744279543/10000000000000 : ℝ)^3111
        have hw : |(-400318053/2000000000 : ℝ)|=(400318053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s2_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272620163/625000000 : ℝ)*x 0 + (948201563/2000000000 : ℝ)*x 1 + (2006902789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272620163/625000000 : ℝ)^4135 ≤ (33195276685779/100000000000000 : ℝ)^3111 := by
    have hnat : (272620163 : ℕ)^4135*100000000000000^3111 ≤ 33195276685779^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272620163 625000000 33195276685779 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948201563/2000000000 : ℝ)^4135 ≤ (9270902552927/25000000000000 : ℝ)^3111 := by
    have hnat : (948201563 : ℕ)^4135*25000000000000^3111 ≤ 9270902552927^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948201563 2000000000 9270902552927 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006902789/5000000000 : ℝ)^4135 ≤ (29721113090923/100000000000000 : ℝ)^3111 := by
    have hnat : (2006902789 : ℕ)^4135*100000000000000^3111 ≤ 29721113090923^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006902789 5000000000 29721113090923 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272620163/625000000 : ℝ), (948201563/2000000000 : ℝ), (2006902789/5000000000 : ℝ)] ![(33195276685779/100000000000000 : ℝ), (9270902552927/25000000000000 : ℝ), (29721113090923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272620163/625000000 : ℝ)|^4135 ≤ (33195276685779/100000000000000 : ℝ)^3111
        have hw : |(272620163/625000000 : ℝ)|=(272620163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(948201563/2000000000 : ℝ)|^4135 ≤ (9270902552927/25000000000000 : ℝ)^3111
        have hw : |(948201563/2000000000 : ℝ)|=(948201563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006902789/5000000000 : ℝ)|^4135 ≤ (29721113090923/100000000000000 : ℝ)^3111
        have hw : |(2006902789/5000000000 : ℝ)|=(2006902789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4383/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3341/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2639/50000 : ℝ) ^ (8269/2048 : ℝ) ≤ (138955385151813/20000000000000000000 : ℝ) := by
    have hpowers : (2639/50000 : ℝ)^8269 ≤ (138955385151813/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2639 : ℕ)^8269*20000000000000000000^2048 ≤ 138955385151813^2048*50000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2639 50000 138955385151813 20000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2639/50000 : ℝ)) (X := (138955385151813/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10369/50000 : ℝ) ^ (8269/2048 : ℝ) ≤ (174332964857931009/100000000000000000000 : ℝ) := by
    have hpowers : (10369/50000 : ℝ)^8269 ≤ (174332964857931009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10369 : ℕ)^8269*100000000000000000000^2048 ≤ 174332964857931009^2048*50000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10369 50000 174332964857931009 100000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10369/50000 : ℝ)) (X := (174332964857931009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000138955385151813/10000000000000000000 : ℝ) ≤ (10000034415182163/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (10000138955385151813/10000000000000000000 : ℝ)^2048 ≤ (10000034415182163/10000000000000000 : ℝ)^8269 := by
      have hnat : (10000138955385151813 : ℕ)^2048*10000000000000000^8269 ≤ 10000034415182163^8269*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000138955385151813 10000000000000000000 10000034415182163 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034415182163/10000000000000000 : ℝ)) (X := (10000138955385151813/10000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50087513870891845037/50000000000000000000 : ℝ) ≤ (5002166048199927/5000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (50087513870891845037/50000000000000000000 : ℝ)^2048 ≤ (5002166048199927/5000000000000000 : ℝ)^8269 := by
      have hnat : (50087513870891845037 : ℕ)^2048*5000000000000000^8269 ≤ 5002166048199927^8269*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50087513870891845037 50000000000000000000 5002166048199927 5000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002166048199927/5000000000000000 : ℝ)) (X := (50087513870891845037/50000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50174332964857931009/50000000000000000000 : ℝ) ≤ (2001725955523509/2000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (50174332964857931009/50000000000000000000 : ℝ)^2048 ≤ (2001725955523509/2000000000000000 : ℝ)^8269 := by
      have hnat : (50174332964857931009 : ℕ)^2048*2000000000000000^8269 ≤ 2001725955523509^8269*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50174332964857931009 50000000000000000000 2001725955523509 2000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001725955523509/2000000000000000 : ℝ)) (X := (50174332964857931009/50000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(138955385151813/20000000000000000000 : ℝ) ≤ ((19319395716972786723/19325000000000000000 : ℝ)+2*(4297681217691/1546000000000000 : ℝ)*(2639/50000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (19319395716972786723/19325000000000000000 : ℝ)+2*(4297681217691/1546000000000000 : ℝ)*(2639/50000 : ℝ)=(10000034415182163/10000000000000000 : ℝ) by norm_num, show 1+2*(138955385151813/20000000000000000000 : ℝ)=(10000138955385151813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(174332964857931009/100000000000000000000 : ℝ)+(138955385151813/20000000000000000000 : ℝ) ≤ ((19319395716972786723/19325000000000000000 : ℝ)+(4297681217691/1546000000000000 : ℝ)*((10369/50000 : ℝ)+(2639/50000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (19319395716972786723/19325000000000000000 : ℝ)+(4297681217691/1546000000000000 : ℝ)*((10369/50000 : ℝ)+(2639/50000 : ℝ))=(5002166048199927/5000000000000000 : ℝ) by norm_num, show 1+(174332964857931009/100000000000000000000 : ℝ)+(138955385151813/20000000000000000000 : ℝ)=(50087513870891845037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(174332964857931009/100000000000000000000 : ℝ) ≤ ((19319395716972786723/19325000000000000000 : ℝ)+2*(4297681217691/1546000000000000 : ℝ)*(10369/50000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (19319395716972786723/19325000000000000000 : ℝ)+2*(4297681217691/1546000000000000 : ℝ)*(10369/50000 : ℝ)=(2001725955523509/2000000000000000 : ℝ) by norm_num, show 1+2*(174332964857931009/100000000000000000000 : ℝ)=(50174332964857931009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19319395716972786723/19325000000000000000 : ℝ)*(X 1 0+X 2 0)+(4297681217691/1546000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2639/50000 : ℝ)) (hi := (10369/50000 : ℝ)) (c := (19319395716972786723/19325000000000000000 : ℝ)) (alpha := (4297681217691/1546000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19319395716972786723/19325000000000000000 : ℝ)*(X 0 1+X 2 1)+(4297681217691/1546000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2639/50000 : ℝ)) (hi := (10369/50000 : ℝ)) (c := (19319395716972786723/19325000000000000000 : ℝ)) (alpha := (4297681217691/1546000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19319395716972786723/19325000000000000000 : ℝ)*(X 0 2+X 1 2)+(4297681217691/1546000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (2639/50000 : ℝ)) (hi := (10369/50000 : ℝ)) (c := (19319395716972786723/19325000000000000000 : ℝ)) (alpha := (4297681217691/1546000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2178704201/10000000000 : ℝ)*X 0 0+(690453353/1250000000 : ℝ)*X 0 1+(2573968251/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376707423/10000000000 : ℝ)*X 1 0+(-474908101/2000000000 : ℝ)*X 1 1+(16087303/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344176899/2500000000 : ℝ)*X 2 0+(2573968389/5000000000 : ℝ)*X 2 1+(-1187270257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361682353/10000000000 : ℝ)*X 0 0+(4008424987/10000000000 : ℝ)*X 0 1+(4746333089/10000000000 : ℝ)*X 0 2+(4361682353/10000000000 : ℝ)*X 1 0+(4008424987/10000000000 : ℝ)*X 1 1+(4746333089/10000000000 : ℝ)*X 1 2+(4361682353/10000000000 : ℝ)*X 2 0+(4008424987/10000000000 : ℝ)*X 2 1+(4746333089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2178826457/10000000000 : ℝ)*X 0 0+(5150647983/10000000000 : ℝ)*X 0 1+(5520887023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281806437/10000000000 : ℝ)*X 1 0+(-250198797/1250000000 : ℝ)*X 1 1+(5520887117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640903339/5000000000 : ℝ)*X 2 0+(2760443479/5000000000 : ℝ)*X 2 1+(-400318053/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272620163/625000000 : ℝ)*X 0 0+(948201563/2000000000 : ℝ)*X 0 1+(2006902789/5000000000 : ℝ)*X 0 2+(272620163/625000000 : ℝ)*X 1 0+(948201563/2000000000 : ℝ)*X 1 1+(2006902789/5000000000 : ℝ)*X 1 2+(272620163/625000000 : ℝ)*X 2 0+(948201563/2000000000 : ℝ)*X 2 1+(2006902789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68006050618228644585573/19325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288962917/50000000000000 : ℝ)*(base19) + (655968977/100000000000000 : ℝ)*(base23) + (14865529/25000000000000 : ℝ)*(upper3) + (817469/20000000000000 : ℝ)*(upper4) + (33772243/50000000000000 : ℝ)*(upper5) + (251060904433587/12500000000000 : ℝ)*(major0) + (251060904433587/12500000000000 : ℝ)*(major1) + (251060904433587/12500000000000 : ℝ)*(major2) + (665443823359537/25000000000000 : ℝ)*(sp0) + (66544597717807/2500000000000 : ℝ)*(sp1) + (1330891915334569/50000000000000 : ℝ)*(sp2) + (1355186001661971/100000000000000 : ℝ)*(sp3) + (9193199967/100000000000000 : ℝ)*(sp4) + (3865334927/100000000000000 : ℝ)*(sp7) + (677594933498449/50000000000000 : ℝ)*(f.failure) + (1330892243319057/50000000000000 : ℝ)*(f.sum) + (6932100607917/9662500000000000000000000000 : ℝ)*base65 + (323608452678109599/241562500000000000000000000000000 : ℝ)*base68 + (621084305394047099/241562500000000000000000000000000 : ℝ)*base70 + (1570758630211890401/241562500000000000000000000000000 : ℝ)*base71 + (6841916436177/2415625000000000000000000000 : ℝ)*base74 + (1457545966700015401/241562500000000000000000000000000 : ℝ)*base75 + (1279707327783109599/241562500000000000000000000000000 : ℝ)*base78 + (391933768627202901/241562500000000000000000000000000 : ℝ)*base79 + (31492783513009/19325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (23670223/5000000000000000000000 : ℝ)*base90 + (23670223/5000000000000000000000 : ℝ)*base92 + (23670223/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1862592950872779029128515819/193250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1895165299/100000000000000 : ℝ)*(base19) + (1088535619/50000000000000 : ℝ)*(base23) + (12529703/5000000000000 : ℝ)*(upper3) + (11478641/20000000000000 : ℝ)*(lower4) + (49752961/25000000000000 : ℝ)*(upper5) + (407609097276149/20000000000000 : ℝ)*(major0) + (407609097276149/20000000000000 : ℝ)*(major1) + (407609097276149/20000000000000 : ℝ)*(major2) + (8361182503/50000000000000 : ℝ)*(sp1) + (19505389749/100000000000000 : ℝ)*(sp2) + (54019137953203/2000000000000 : ℝ)*(sp4) + (1350469140064923/50000000000000 : ℝ)*(sp5) + (2700935215199163/100000000000000 : ℝ)*(sp6) + (687566876913069/50000000000000 : ℝ)*(sp7) + (687566876913069/50000000000000 : ℝ)*(f.failure) + (54019137953203/2000000000000 : ℝ)*(f.sum) + (40477791260881/15460000000000000000000000000 : ℝ)*base66 + (829119971468742773/386500000000000000000000000000000 : ℝ)*base68 + (2858327612400257227/386500000000000000000000000000000 : ℝ)*base69 + (1493722268044742773/386500000000000000000000000000000 : ℝ)*base72 + (8147016353719/15460000000000000000000000000 : ℝ)*base73 + (667884356542257227/386500000000000000000000000000000 : ℝ)*base75 + (458881267408257227/386500000000000000000000000000000 : ℝ)*base77 + (2470226678382257227/386500000000000000000000000000000 : ℝ)*base79 + (38987857458779/15460000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (18062963/5000000000000000000000 : ℝ)*base90 + (18062963/5000000000000000000000 : ℝ)*base92 + (18062963/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1077_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1077_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1077_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1077_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1077_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3341/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
