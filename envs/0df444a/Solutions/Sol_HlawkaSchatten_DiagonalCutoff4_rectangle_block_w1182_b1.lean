-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:08.767797+00:00
-- url     : https://prove2.me/submissions/d8db370d-e786-460a-9b9b-7a36cb5c9e0c

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
theorem support_rectangle_w1182_s3_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268064557/1250000000 : ℝ)*x 0 + (5425177281/10000000000 : ℝ)*x 1 + (5235710613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268064557/1250000000 : ℝ)^8375 ≤ (13028246835133/100000000000000 : ℝ)^6327 := by
    have hnat : (268064557 : ℕ)^8375*100000000000000^6327 ≤ 13028246835133^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268064557 1250000000 13028246835133 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425177281/10000000000 : ℝ)^8375 ≤ (11127198312679/25000000000000 : ℝ)^6327 := by
    have hnat : (5425177281 : ℕ)^8375*25000000000000^6327 ≤ 11127198312679^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425177281 10000000000 11127198312679 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235710613/10000000000 : ℝ)^8375 ≤ (42462959895843/100000000000000 : ℝ)^6327 := by
    have hnat : (5235710613 : ℕ)^8375*100000000000000^6327 ≤ 42462959895843^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235710613 10000000000 42462959895843 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268064557/1250000000 : ℝ), (5425177281/10000000000 : ℝ), (5235710613/10000000000 : ℝ)] ![(13028246835133/100000000000000 : ℝ), (11127198312679/25000000000000 : ℝ), (42462959895843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268064557/1250000000 : ℝ)|^8375 ≤ (13028246835133/100000000000000 : ℝ)^6327
        have hw : |(-268064557/1250000000 : ℝ)|=(268064557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425177281/10000000000 : ℝ)|^8375 ≤ (11127198312679/25000000000000 : ℝ)^6327
        have hw : |(5425177281/10000000000 : ℝ)|=(5425177281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235710613/10000000000 : ℝ)|^8375 ≤ (42462959895843/100000000000000 : ℝ)^6327
        have hw : |(5235710613/10000000000 : ℝ)|=(5235710613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352847149/10000000000 : ℝ)*x 0 + (-2241283187/10000000000 : ℝ)*x 1 + (5235710419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352847149/10000000000 : ℝ)^8375 ≤ (43725007866719/100000000000000 : ℝ)^6327 := by
    have hnat : (5352847149 : ℕ)^8375*100000000000000^6327 ≤ 43725007866719^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352847149 10000000000 43725007866719 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241283187/10000000000 : ℝ)^8375 ≤ (863252144117/6250000000000 : ℝ)^6327 := by
    have hnat : (2241283187 : ℕ)^8375*6250000000000^6327 ≤ 863252144117^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241283187 10000000000 863252144117 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235710419/10000000000 : ℝ)^8375 ≤ (1061573945329/2500000000000 : ℝ)^6327 := by
    have hnat : (5235710419 : ℕ)^8375*2500000000000^6327 ≤ 1061573945329^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235710419 10000000000 1061573945329 2500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352847149/10000000000 : ℝ), (-2241283187/10000000000 : ℝ), (5235710419/10000000000 : ℝ)] ![(43725007866719/100000000000000 : ℝ), (863252144117/6250000000000 : ℝ), (1061573945329/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352847149/10000000000 : ℝ)|^8375 ≤ (43725007866719/100000000000000 : ℝ)^6327
        have hw : |(5352847149/10000000000 : ℝ)|=(5352847149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241283187/10000000000 : ℝ)|^8375 ≤ (863252144117/6250000000000 : ℝ)^6327
        have hw : |(-2241283187/10000000000 : ℝ)|=(2241283187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235710419/10000000000 : ℝ)|^8375 ≤ (1061573945329/2500000000000 : ℝ)^6327
        have hw : |(5235710419/10000000000 : ℝ)|=(5235710419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352847237/10000000000 : ℝ)*x 0 + (5235710383/10000000000 : ℝ)*x 1 + (-1120641559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352847237/10000000000 : ℝ)^8375 ≤ (5465626102279/12500000000000 : ℝ)^6327 := by
    have hnat : (5352847237 : ℕ)^8375*12500000000000^6327 ≤ 5465626102279^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352847237 10000000000 5465626102279 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235710383/10000000000 : ℝ)^8375 ≤ (21231478713341/50000000000000 : ℝ)^6327 := by
    have hnat : (5235710383 : ℕ)^8375*50000000000000^6327 ≤ 21231478713341^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235710383 10000000000 21231478713341 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120641559/5000000000 : ℝ)^8375 ≤ (13812033743017/100000000000000 : ℝ)^6327 := by
    have hnat : (1120641559 : ℕ)^8375*100000000000000^6327 ≤ 13812033743017^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120641559 5000000000 13812033743017 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352847237/10000000000 : ℝ), (5235710383/10000000000 : ℝ), (-1120641559/5000000000 : ℝ)] ![(5465626102279/12500000000000 : ℝ), (21231478713341/50000000000000 : ℝ), (13812033743017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352847237/10000000000 : ℝ)|^8375 ≤ (5465626102279/12500000000000 : ℝ)^6327
        have hw : |(5352847237/10000000000 : ℝ)|=(5352847237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235710383/10000000000 : ℝ)|^8375 ≤ (21231478713341/50000000000000 : ℝ)^6327
        have hw : |(5235710383/10000000000 : ℝ)|=(5235710383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120641559/5000000000 : ℝ)|^8375 ≤ (13812033743017/100000000000000 : ℝ)^6327
        have hw : |(-1120641559/5000000000 : ℝ)|=(1120641559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357053851/10000000000 : ℝ)*x 0 + (417118121/1000000000 : ℝ)*x 1 + (2275540001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357053851/10000000000 : ℝ)^8375 ≤ (665936040533/2000000000000 : ℝ)^6327 := by
    have hnat : (4357053851 : ℕ)^8375*2000000000000^6327 ≤ 665936040533^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357053851 10000000000 665936040533 2000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417118121/1000000000 : ℝ)^8375 ≤ (31429676382761/100000000000000 : ℝ)^6327 := by
    have hnat : (417118121 : ℕ)^8375*100000000000000^6327 ≤ 31429676382761^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417118121 1000000000 31429676382761 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275540001/5000000000 : ℝ)^8375 ≤ (8818380394753/25000000000000 : ℝ)^6327 := by
    have hnat : (2275540001 : ℕ)^8375*25000000000000^6327 ≤ 8818380394753^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275540001 5000000000 8818380394753 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357053851/10000000000 : ℝ), (417118121/1000000000 : ℝ), (2275540001/5000000000 : ℝ)] ![(665936040533/2000000000000 : ℝ), (31429676382761/100000000000000 : ℝ), (8818380394753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357053851/10000000000 : ℝ)|^8375 ≤ (665936040533/2000000000000 : ℝ)^6327
        have hw : |(4357053851/10000000000 : ℝ)|=(4357053851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417118121/1000000000 : ℝ)|^8375 ≤ (31429676382761/100000000000000 : ℝ)^6327
        have hw : |(417118121/1000000000 : ℝ)|=(417118121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2275540001/5000000000 : ℝ)|^8375 ≤ (8818380394753/25000000000000 : ℝ)^6327
        have hw : |(2275540001/5000000000 : ℝ)|=(2275540001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144532703/10000000000 : ℝ)*x 0 + (1309106513/2500000000 : ℝ)*x 1 + (1084891593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144532703/10000000000 : ℝ)^8375 ≤ (6514188743751/50000000000000 : ℝ)^6327 := by
    have hnat : (2144532703 : ℕ)^8375*50000000000000^6327 ≤ 6514188743751^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144532703 10000000000 6514188743751 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309106513/2500000000 : ℝ)^8375 ≤ (42470640649309/100000000000000 : ℝ)^6327 := by
    have hnat : (1309106513 : ℕ)^8375*100000000000000^6327 ≤ 42470640649309^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309106513 2500000000 42470640649309 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084891593/2000000000 : ℝ)^8375 ≤ (8900196368741/20000000000000 : ℝ)^6327 := by
    have hnat : (1084891593 : ℕ)^8375*20000000000000^6327 ≤ 8900196368741^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084891593 2000000000 8900196368741 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144532703/10000000000 : ℝ), (1309106513/2500000000 : ℝ), (1084891593/2000000000 : ℝ)] ![(6514188743751/50000000000000 : ℝ), (42470640649309/100000000000000 : ℝ), (8900196368741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144532703/10000000000 : ℝ)|^8375 ≤ (6514188743751/50000000000000 : ℝ)^6327
        have hw : |(-2144532703/10000000000 : ℝ)|=(2144532703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309106513/2500000000 : ℝ)|^8375 ≤ (42470640649309/100000000000000 : ℝ)^6327
        have hw : |(1309106513/2500000000 : ℝ)|=(1309106513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084891593/2000000000 : ℝ)|^8375 ≤ (8900196368741/20000000000000 : ℝ)^6327
        have hw : |(1084891593/2000000000 : ℝ)|=(1084891593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060941747/2000000000 : ℝ)*x 0 + (-2052535403/10000000000 : ℝ)*x 1 + (2712228959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060941747/2000000000 : ℝ)^8375 ≤ (21602631652899/50000000000000 : ℝ)^6327 := by
    have hnat : (1060941747 : ℕ)^8375*50000000000000^6327 ≤ 21602631652899^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060941747 2000000000 21602631652899 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052535403/10000000000 : ℝ)^8375 ≤ (12293755348057/100000000000000 : ℝ)^6327 := by
    have hnat : (2052535403 : ℕ)^8375*100000000000000^6327 ≤ 12293755348057^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052535403 10000000000 12293755348057 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712228959/5000000000 : ℝ)^8375 ≤ (1112524533333/2500000000000 : ℝ)^6327 := by
    have hnat : (2712228959 : ℕ)^8375*2500000000000^6327 ≤ 1112524533333^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712228959 5000000000 1112524533333 2500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060941747/2000000000 : ℝ), (-2052535403/10000000000 : ℝ), (2712228959/5000000000 : ℝ)] ![(21602631652899/50000000000000 : ℝ), (12293755348057/100000000000000 : ℝ), (1112524533333/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060941747/2000000000 : ℝ)|^8375 ≤ (21602631652899/50000000000000 : ℝ)^6327
        have hw : |(1060941747/2000000000 : ℝ)|=(1060941747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052535403/10000000000 : ℝ)|^8375 ≤ (12293755348057/100000000000000 : ℝ)^6327
        have hw : |(-2052535403/10000000000 : ℝ)|=(2052535403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712228959/5000000000 : ℝ)|^8375 ≤ (1112524533333/2500000000000 : ℝ)^6327
        have hw : |(2712228959/5000000000 : ℝ)|=(2712228959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304708401/10000000000 : ℝ)*x 0 + (1084891657/2000000000 : ℝ)*x 1 + (-1026267677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304708401/10000000000 : ℝ)^8375 ≤ (43205259704919/100000000000000 : ℝ)^6327 := by
    have hnat : (5304708401 : ℕ)^8375*100000000000000^6327 ≤ 43205259704919^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304708401 10000000000 43205259704919 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084891657/2000000000 : ℝ)^8375 ≤ (44500985318669/100000000000000 : ℝ)^6327 := by
    have hnat : (1084891657 : ℕ)^8375*100000000000000^6327 ≤ 44500985318669^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084891657 2000000000 44500985318669 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026267677/5000000000 : ℝ)^8375 ≤ (1229375495957/10000000000000 : ℝ)^6327 := by
    have hnat : (1026267677 : ℕ)^8375*10000000000000^6327 ≤ 1229375495957^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026267677 5000000000 1229375495957 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304708401/10000000000 : ℝ), (1084891657/2000000000 : ℝ), (-1026267677/5000000000 : ℝ)] ![(43205259704919/100000000000000 : ℝ), (44500985318669/100000000000000 : ℝ), (1229375495957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304708401/10000000000 : ℝ)|^8375 ≤ (43205259704919/100000000000000 : ℝ)^6327
        have hw : |(5304708401/10000000000 : ℝ)|=(5304708401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084891657/2000000000 : ℝ)|^8375 ≤ (44500985318669/100000000000000 : ℝ)^6327
        have hw : |(1084891657/2000000000 : ℝ)|=(1084891657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026267677/5000000000 : ℝ)|^8375 ≤ (1229375495957/10000000000000 : ℝ)^6327
        have hw : |(-1026267677/5000000000 : ℝ)|=(1026267677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s3_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089271677/2500000000 : ℝ)*x 0 + (4549645139/10000000000 : ℝ)*x 1 + (2086311827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089271677/2500000000 : ℝ)^8375 ≤ (16648567199549/50000000000000 : ℝ)^6327 := by
    have hnat : (1089271677 : ℕ)^8375*50000000000000^6327 ≤ 16648567199549^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089271677 2500000000 16648567199549 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549645139/10000000000 : ℝ)^8375 ≤ (4407350189769/12500000000000 : ℝ)^6327 := by
    have hnat : (4549645139 : ℕ)^8375*12500000000000^6327 ≤ 4407350189769^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549645139 10000000000 4407350189769 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086311827/5000000000 : ℝ)^8375 ≤ (31444064073653/100000000000000 : ℝ)^6327 := by
    have hnat : (2086311827 : ℕ)^8375*100000000000000^6327 ≤ 31444064073653^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086311827 5000000000 31444064073653 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089271677/2500000000 : ℝ), (4549645139/10000000000 : ℝ), (2086311827/5000000000 : ℝ)] ![(16648567199549/50000000000000 : ℝ), (4407350189769/12500000000000 : ℝ), (31444064073653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089271677/2500000000 : ℝ)|^8375 ≤ (16648567199549/50000000000000 : ℝ)^6327
        have hw : |(1089271677/2500000000 : ℝ)|=(1089271677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549645139/10000000000 : ℝ)|^8375 ≤ (4407350189769/12500000000000 : ℝ)^6327
        have hw : |(4549645139/10000000000 : ℝ)|=(4549645139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086311827/5000000000 : ℝ)|^8375 ≤ (31444064073653/100000000000000 : ℝ)^6327
        have hw : |(2086311827/5000000000 : ℝ)|=(2086311827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (43/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8193/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (289/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8193/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (289/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8193/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (289/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8193/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (289/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8193/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (289/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8193/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (289/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (289/3125 : ℝ) ^ (4187/1024 : ℝ) ≤ (5919797652649087/100000000000000000000 : ℝ) := by
    have hpowers : (289/3125 : ℝ)^4187 ≤ (5919797652649087/100000000000000000000 : ℝ)^1024 := by
      have hnat : (289 : ℕ)^4187*100000000000000000000^1024 ≤ 5919797652649087^1024*3125^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        289 3125 5919797652649087 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (289/3125 : ℝ)) (X := (5919797652649087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8193/50000 : ℝ) ^ (4187/1024 : ℝ) ≤ (30694052162551367/50000000000000000000 : ℝ) := by
    have hpowers : (8193/50000 : ℝ)^4187 ≤ (30694052162551367/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8193 : ℕ)^4187*50000000000000000000^1024 ≤ 30694052162551367^1024*50000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8193 50000 30694052162551367 50000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8193/50000 : ℝ)) (X := (30694052162551367/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005919797652649087/50000000000000000000 : ℝ) ≤ (5000144771954319/5000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50005919797652649087/50000000000000000000 : ℝ)^1024 ≤ (5000144771954319/5000000000000000 : ℝ)^4187 := by
      have hnat : (50005919797652649087 : ℕ)^1024*5000000000000000^4187 ≤ 5000144771954319^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005919797652649087 50000000000000000000 5000144771954319 5000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144771954319/5000000000000000 : ℝ)) (X := (50005919797652649087/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100067307901977751821/100000000000000000000 : ℝ) ≤ (500082285378473/500000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (100067307901977751821/100000000000000000000 : ℝ)^1024 ≤ (500082285378473/500000000000000 : ℝ)^4187 := by
      have hnat : (100067307901977751821 : ℕ)^1024*500000000000000^4187 ≤ 500082285378473^4187*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100067307901977751821 100000000000000000000 500082285378473 500000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500082285378473/500000000000000 : ℝ)) (X := (100067307901977751821/100000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030694052162551367/25000000000000000000 : ℝ) ≤ (5001500935615141/5000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (25030694052162551367/25000000000000000000 : ℝ)^1024 ≤ (5001500935615141/5000000000000000 : ℝ)^4187 := by
      have hnat : (25030694052162551367 : ℕ)^1024*5000000000000000^4187 ≤ 5001500935615141^4187*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030694052162551367 25000000000000000000 5001500935615141 5000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001500935615141/5000000000000000 : ℝ)) (X := (25030694052162551367/25000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5919797652649087/100000000000000000000 : ℝ) ≤ ((17839245790337323583/17845000000000000000 : ℝ)+2*(678081830411/356900000000000 : ℝ)*(289/3125 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (17839245790337323583/17845000000000000000 : ℝ)+2*(678081830411/356900000000000 : ℝ)*(289/3125 : ℝ)=(5000144771954319/5000000000000000 : ℝ) by norm_num, show 1+2*(5919797652649087/100000000000000000000 : ℝ)=(50005919797652649087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30694052162551367/50000000000000000000 : ℝ)+(5919797652649087/100000000000000000000 : ℝ) ≤ ((17839245790337323583/17845000000000000000 : ℝ)+(678081830411/356900000000000 : ℝ)*((8193/50000 : ℝ)+(289/3125 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (17839245790337323583/17845000000000000000 : ℝ)+(678081830411/356900000000000 : ℝ)*((8193/50000 : ℝ)+(289/3125 : ℝ))=(500082285378473/500000000000000 : ℝ) by norm_num, show 1+(30694052162551367/50000000000000000000 : ℝ)+(5919797652649087/100000000000000000000 : ℝ)=(100067307901977751821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30694052162551367/50000000000000000000 : ℝ) ≤ ((17839245790337323583/17845000000000000000 : ℝ)+2*(678081830411/356900000000000 : ℝ)*(8193/50000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (17839245790337323583/17845000000000000000 : ℝ)+2*(678081830411/356900000000000 : ℝ)*(8193/50000 : ℝ)=(5001500935615141/5000000000000000 : ℝ) by norm_num, show 1+2*(30694052162551367/50000000000000000000 : ℝ)=(25030694052162551367/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17839245790337323583/17845000000000000000 : ℝ)*(X 1 0+X 2 0)+(678081830411/356900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (289/3125 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (17839245790337323583/17845000000000000000 : ℝ)) (alpha := (678081830411/356900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17839245790337323583/17845000000000000000 : ℝ)*(X 0 1+X 2 1)+(678081830411/356900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (289/3125 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (17839245790337323583/17845000000000000000 : ℝ)) (alpha := (678081830411/356900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17839245790337323583/17845000000000000000 : ℝ)*(X 0 2+X 1 2)+(678081830411/356900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (289/3125 : ℝ)) (hi := (8193/50000 : ℝ)) (c := (17839245790337323583/17845000000000000000 : ℝ)) (alpha := (678081830411/356900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268064557/1250000000 : ℝ)*X 0 0+(5425177281/10000000000 : ℝ)*X 0 1+(5235710613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352847149/10000000000 : ℝ)*X 1 0+(-2241283187/10000000000 : ℝ)*X 1 1+(5235710419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352847237/10000000000 : ℝ)*X 2 0+(5235710383/10000000000 : ℝ)*X 2 1+(-1120641559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357053851/10000000000 : ℝ)*X 0 0+(417118121/1000000000 : ℝ)*X 0 1+(2275540001/5000000000 : ℝ)*X 0 2+(4357053851/10000000000 : ℝ)*X 1 0+(417118121/1000000000 : ℝ)*X 1 1+(2275540001/5000000000 : ℝ)*X 1 2+(4357053851/10000000000 : ℝ)*X 2 0+(417118121/1000000000 : ℝ)*X 2 1+(2275540001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144532703/10000000000 : ℝ)*X 0 0+(1309106513/2500000000 : ℝ)*X 0 1+(1084891593/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060941747/2000000000 : ℝ)*X 1 0+(-2052535403/10000000000 : ℝ)*X 1 1+(2712228959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304708401/10000000000 : ℝ)*X 2 0+(1084891657/2000000000 : ℝ)*X 2 1+(-1026267677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089271677/2500000000 : ℝ)*X 0 0+(4549645139/10000000000 : ℝ)*X 0 1+(2086311827/5000000000 : ℝ)*X 0 2+(1089271677/2500000000 : ℝ)*X 1 0+(4549645139/10000000000 : ℝ)*X 1 1+(2086311827/5000000000 : ℝ)*X 1 2+(1089271677/2500000000 : ℝ)*X 2 0+(4549645139/10000000000 : ℝ)*X 2 1+(2086311827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (443955131483821044458279319/44612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223927621/10000000000000 : ℝ)*(base19) + (2161317747/100000000000000 : ℝ)*(base23) + (5511049/6250000000000 : ℝ)*(lower2) + (238314189/100000000000000 : ℝ)*(upper3) + (407161/200000000000 : ℝ)*(upper5) + (395518385123569/10000000000000 : ℝ)*(major0) + (395518385123569/10000000000000 : ℝ)*(major1) + (395518385123569/10000000000000 : ℝ)*(major2) + (164937820992997/3125000000000 : ℝ)*(sp0) + (2639023252220303/50000000000000 : ℝ)*(sp1) + (527804658239907/10000000000000 : ℝ)*(sp2) + (1316149270609129/50000000000000 : ℝ)*(sp3) + (38471940913/100000000000000 : ℝ)*(sp4) + (4017164847/20000000000000 : ℝ)*(sp7) + (1316159313521247/50000000000000 : ℝ)*(f.failure) + (329878046482301/6250000000000 : ℝ)*(f.sum) + (9296231465843/3569000000000000000000000000 : ℝ)*base65 + (1473829303370527727/178450000000000000000000000000000 : ℝ)*base67 + (768724018779572273/178450000000000000000000000000000 : ℝ)*base70 + (1274726591235377727/178450000000000000000000000000000 : ℝ)*base71 + (15441840151131/3569000000000000000000000000 : ℝ)*base73 + (812667275371777727/178450000000000000000000000000000 : ℝ)*base75 + (1093789480764177727/178450000000000000000000000000000 : ℝ)*base77 + (27199161601027727/178450000000000000000000000000000 : ℝ)*base79 + (2770604933139/892250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (28236991/5000000000000000000000 : ℝ)*base89 + (28236991/5000000000000000000000 : ℝ)*base91 + (28236991/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3594966632209529303142478191/892250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341021437/25000000000000 : ℝ)*(base19) + (1273407197/100000000000000 : ℝ)*(base23) + (19398271/25000000000000 : ℝ)*(upper3) + (120293387/100000000000000 : ℝ)*(lower4) + (42603579/25000000000000 : ℝ)*(upper5) + (3985305249384647/100000000000000 : ℝ)*(major0) + (3985305249384647/100000000000000 : ℝ)*(major1) + (3985305249384647/100000000000000 : ℝ)*(major2) + (27632384177/100000000000000 : ℝ)*(sp1) + (7387566119/25000000000000 : ℝ)*(sp2) + (33239030325117/625000000000 : ℝ)*(sp4) + (2659107927774397/50000000000000 : ℝ)*(sp5) + (2659107014173523/50000000000000 : ℝ)*(sp6) + (663091378111787/25000000000000 : ℝ)*(sp7) + (663091378111787/25000000000000 : ℝ)*(f.failure) + (33239030325117/625000000000 : ℝ)*(f.sum) + (19663947704637/17845000000000000000000000000 : ℝ)*base65 + (19806656259753080201/1784500000000000000000000000000000 : ℝ)*base67 + (9719169382743080201/1784500000000000000000000000000000 : ℝ)*base69 + (17788246257145580201/1784500000000000000000000000000000 : ℝ)*base71 + (26930884511511/8922500000000000000000000000 : ℝ)*base73 + (36227584510695580201/1784500000000000000000000000000000 : ℝ)*base75 + (13580557120218080201/1784500000000000000000000000000000 : ℝ)*base77 + (27445142522512080201/1784500000000000000000000000000000 : ℝ)*base79 + (17527703977383/17845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12926389/2500000000000000000000 : ℝ)*base90 + (12926389/2500000000000000000000 : ℝ)*base92 + (12926389/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1182_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s4_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147214679/10000000000 : ℝ)*x 0 + (5400041301/10000000000 : ℝ)*x 1 + (210363199/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147214679/10000000000 : ℝ)^8375 ≤ (13049949337853/100000000000000 : ℝ)^6327 := by
    have hnat : (2147214679 : ℕ)^8375*100000000000000^6327 ≤ 13049949337853^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147214679 10000000000 13049949337853 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400041301/10000000000 : ℝ)^8375 ≤ (22118014150601/50000000000000 : ℝ)^6327 := by
    have hnat : (5400041301 : ℕ)^8375*50000000000000^6327 ≤ 22118014150601^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400041301 10000000000 22118014150601 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210363199/400000000 : ℝ)^8375 ≤ (21357011174923/50000000000000 : ℝ)^6327 := by
    have hnat : (210363199 : ℕ)^8375*50000000000000^6327 ≤ 21357011174923^6327*400000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210363199 400000000 21357011174923 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147214679/10000000000 : ℝ), (5400041301/10000000000 : ℝ), (210363199/400000000 : ℝ)] ![(13049949337853/100000000000000 : ℝ), (22118014150601/50000000000000 : ℝ), (21357011174923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147214679/10000000000 : ℝ)|^8375 ≤ (13049949337853/100000000000000 : ℝ)^6327
        have hw : |(-2147214679/10000000000 : ℝ)|=(2147214679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400041301/10000000000 : ℝ)|^8375 ≤ (22118014150601/50000000000000 : ℝ)^6327
        have hw : |(5400041301/10000000000 : ℝ)|=(5400041301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210363199/400000000 : ℝ)|^8375 ≤ (21357011174923/50000000000000 : ℝ)^6327
        have hw : |(210363199/400000000 : ℝ)|=(210363199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534654431/1000000000 : ℝ)*x 0 + (-2218821231/10000000000 : ℝ)*x 1 + (1051816079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534654431/1000000000 : ℝ)^8375 ≤ (10914217620677/25000000000000 : ℝ)^6327 := by
    have hnat : (534654431 : ℕ)^8375*25000000000000^6327 ≤ 10914217620677^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534654431 1000000000 10914217620677 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218821231/10000000000 : ℝ)^8375 ≤ (545164105981/4000000000000 : ℝ)^6327 := by
    have hnat : (2218821231 : ℕ)^8375*4000000000000^6327 ≤ 545164105981^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218821231 10000000000 545164105981 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051816079/2000000000 : ℝ)^8375 ≤ (21357013432627/50000000000000 : ℝ)^6327 := by
    have hnat : (1051816079 : ℕ)^8375*50000000000000^6327 ≤ 21357013432627^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051816079 2000000000 21357013432627 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534654431/1000000000 : ℝ), (-2218821231/10000000000 : ℝ), (1051816079/2000000000 : ℝ)] ![(10914217620677/25000000000000 : ℝ), (545164105981/4000000000000 : ℝ), (21357013432627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534654431/1000000000 : ℝ)|^8375 ≤ (10914217620677/25000000000000 : ℝ)^6327
        have hw : |(534654431/1000000000 : ℝ)|=(534654431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2218821231/10000000000 : ℝ)|^8375 ≤ (545164105981/4000000000000 : ℝ)^6327
        have hw : |(-2218821231/10000000000 : ℝ)|=(2218821231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051816079/2000000000 : ℝ)|^8375 ≤ (21357013432627/50000000000000 : ℝ)^6327
        have hw : |(1051816079/2000000000 : ℝ)|=(1051816079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336636063/2500000000 : ℝ)*x 0 + (1314770253/2500000000 : ℝ)*x 1 + (-2218820491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336636063/2500000000 : ℝ)^8375 ≤ (43656869855813/100000000000000 : ℝ)^6327 := by
    have hnat : (1336636063 : ℕ)^8375*100000000000000^6327 ≤ 43656869855813^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336636063 2500000000 43656869855813 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314770253/2500000000 : ℝ)^8375 ≤ (42714033498603/100000000000000 : ℝ)^6327 := by
    have hnat : (1314770253 : ℕ)^8375*100000000000000^6327 ≤ 42714033498603^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314770253 2500000000 42714033498603 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218820491/10000000000 : ℝ)^8375 ≤ (851818539547/6250000000000 : ℝ)^6327 := by
    have hnat : (2218820491 : ℕ)^8375*6250000000000^6327 ≤ 851818539547^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218820491 10000000000 851818539547 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336636063/2500000000 : ℝ), (1314770253/2500000000 : ℝ), (-2218820491/10000000000 : ℝ)] ![(43656869855813/100000000000000 : ℝ), (42714033498603/100000000000000 : ℝ), (851818539547/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336636063/2500000000 : ℝ)|^8375 ≤ (43656869855813/100000000000000 : ℝ)^6327
        have hw : |(1336636063/2500000000 : ℝ)|=(1336636063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314770253/2500000000 : ℝ)|^8375 ≤ (42714033498603/100000000000000 : ℝ)^6327
        have hw : |(1314770253/2500000000 : ℝ)|=(1314770253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218820491/10000000000 : ℝ)|^8375 ≤ (851818539547/6250000000000 : ℝ)^6327
        have hw : |(-2218820491/10000000000 : ℝ)|=(2218820491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871733201/2000000000 : ℝ)*x 0 + (1054900663/2500000000 : ℝ)*x 1 + (2251121377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871733201/2000000000 : ℝ)^8375 ≤ (8328277773323/25000000000000 : ℝ)^6327 := by
    have hnat : (871733201 : ℕ)^8375*25000000000000^6327 ≤ 8328277773323^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871733201 2000000000 8328277773323 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054900663/2500000000 : ℝ)^8375 ≤ (7978383788469/25000000000000 : ℝ)^6327 := by
    have hnat : (1054900663 : ℕ)^8375*25000000000000^6327 ≤ 7978383788469^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054900663 2500000000 7978383788469 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251121377/5000000000 : ℝ)^8375 ≤ (17386676872077/50000000000000 : ℝ)^6327 := by
    have hnat : (2251121377 : ℕ)^8375*50000000000000^6327 ≤ 17386676872077^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251121377 5000000000 17386676872077 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871733201/2000000000 : ℝ), (1054900663/2500000000 : ℝ), (2251121377/5000000000 : ℝ)] ![(8328277773323/25000000000000 : ℝ), (7978383788469/25000000000000 : ℝ), (17386676872077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871733201/2000000000 : ℝ)|^8375 ≤ (8328277773323/25000000000000 : ℝ)^6327
        have hw : |(871733201/2000000000 : ℝ)|=(871733201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054900663/2500000000 : ℝ)|^8375 ≤ (7978383788469/25000000000000 : ℝ)^6327
        have hw : |(1054900663/2500000000 : ℝ)|=(1054900663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251121377/5000000000 : ℝ)|^8375 ≤ (17386676872077/50000000000000 : ℝ)^6327
        have hw : |(2251121377/5000000000 : ℝ)|=(2251121377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268402679/1250000000 : ℝ)*x 0 + (2629738441/5000000000 : ℝ)*x 1 + (2699821379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268402679/1250000000 : ℝ)^8375 ≤ (3262500916263/25000000000000 : ℝ)^6327 := by
    have hnat : (268402679 : ℕ)^8375*25000000000000^6327 ≤ 3262500916263^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268402679 1250000000 3262500916263 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629738441/5000000000 : ℝ)^8375 ≤ (42718289537479/100000000000000 : ℝ)^6327 := by
    have hnat : (2629738441 : ℕ)^8375*100000000000000^6327 ≤ 42718289537479^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629738441 5000000000 42718289537479 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699821379/5000000000 : ℝ)^8375 ≤ (221158533931/500000000000 : ℝ)^6327 := by
    have hnat : (2699821379 : ℕ)^8375*500000000000^6327 ≤ 221158533931^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699821379 5000000000 221158533931 500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268402679/1250000000 : ℝ), (2629738441/5000000000 : ℝ), (2699821379/5000000000 : ℝ)] ![(3262500916263/25000000000000 : ℝ), (42718289537479/100000000000000 : ℝ), (221158533931/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268402679/1250000000 : ℝ)|^8375 ≤ (3262500916263/25000000000000 : ℝ)^6327
        have hw : |(-268402679/1250000000 : ℝ)|=(268402679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629738441/5000000000 : ℝ)|^8375 ≤ (42718289537479/100000000000000 : ℝ)^6327
        have hw : |(2629738441/5000000000 : ℝ)|=(2629738441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699821379/5000000000 : ℝ)|^8375 ≤ (221158533931/500000000000 : ℝ)^6327
        have hw : |(2699821379/5000000000 : ℝ)|=(2699821379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26553647/50000000 : ℝ)*x 0 + (-2078258351/10000000000 : ℝ)*x 1 + (2699821437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26553647/50000000 : ℝ)^8375 ≤ (43270184470871/100000000000000 : ℝ)^6327 := by
    have hnat : (26553647 : ℕ)^8375*100000000000000^6327 ≤ 43270184470871^6327*50000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26553647 50000000 43270184470871 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078258351/10000000000 : ℝ)^8375 ≤ (6249053733939/50000000000000 : ℝ)^6327 := by
    have hnat : (2078258351 : ℕ)^8375*50000000000000^6327 ≤ 6249053733939^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078258351 10000000000 6249053733939 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699821437/5000000000 : ℝ)^8375 ≤ (22115854022003/50000000000000 : ℝ)^6327 := by
    have hnat : (2699821437 : ℕ)^8375*50000000000000^6327 ≤ 22115854022003^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699821437 5000000000 22115854022003 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26553647/50000000 : ℝ), (-2078258351/10000000000 : ℝ), (2699821437/5000000000 : ℝ)] ![(43270184470871/100000000000000 : ℝ), (6249053733939/50000000000000 : ℝ), (22115854022003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26553647/50000000 : ℝ)|^8375 ≤ (43270184470871/100000000000000 : ℝ)^6327
        have hw : |(26553647/50000000 : ℝ)|=(26553647/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078258351/10000000000 : ℝ)|^8375 ≤ (6249053733939/50000000000000 : ℝ)^6327
        have hw : |(-2078258351/10000000000 : ℝ)|=(2078258351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699821437/5000000000 : ℝ)|^8375 ≤ (22115854022003/50000000000000 : ℝ)^6327
        have hw : |(2699821437/5000000000 : ℝ)|=(2699821437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310729557/10000000000 : ℝ)*x 0 + (5399642631/10000000000 : ℝ)*x 1 + (-2078258471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310729557/10000000000 : ℝ)^8375 ≤ (43270186164121/100000000000000 : ℝ)^6327 := by
    have hnat : (5310729557 : ℕ)^8375*100000000000000^6327 ≤ 43270186164121^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310729557 10000000000 43270186164121 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399642631/10000000000 : ℝ)^8375 ≤ (276448158807/625000000000 : ℝ)^6327 := by
    have hnat : (5399642631 : ℕ)^8375*625000000000^6327 ≤ 276448158807^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399642631 10000000000 276448158807 625000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078258471/10000000000 : ℝ)^8375 ≤ (12498108423119/100000000000000 : ℝ)^6327 := by
    have hnat : (2078258471 : ℕ)^8375*100000000000000^6327 ≤ 12498108423119^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078258471 10000000000 12498108423119 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310729557/10000000000 : ℝ), (5399642631/10000000000 : ℝ), (-2078258471/10000000000 : ℝ)] ![(43270186164121/100000000000000 : ℝ), (276448158807/625000000000 : ℝ), (12498108423119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310729557/10000000000 : ℝ)|^8375 ≤ (43270186164121/100000000000000 : ℝ)^6327
        have hw : |(5310729557/10000000000 : ℝ)|=(5310729557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399642631/10000000000 : ℝ)|^8375 ≤ (276448158807/625000000000 : ℝ)^6327
        have hw : |(5399642631/10000000000 : ℝ)|=(5399642631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078258471/10000000000 : ℝ)|^8375 ≤ (12498108423119/100000000000000 : ℝ)^6327
        have hw : |(-2078258471/10000000000 : ℝ)|=(2078258471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s4_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217933929/500000000 : ℝ)*x 0 + (4501447413/10000000000 : ℝ)*x 1 + (844080421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217933929/500000000 : ℝ)^8375 ≤ (33313238313699/100000000000000 : ℝ)^6327 := by
    have hnat : (217933929 : ℕ)^8375*100000000000000^6327 ≤ 33313238313699^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217933929 500000000 33313238313699 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501447413/10000000000 : ℝ)^8375 ≤ (6953044542673/20000000000000 : ℝ)^6327 := by
    have hnat : (4501447413 : ℕ)^8375*20000000000000^6327 ≤ 6953044542673^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501447413 10000000000 6953044542673 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844080421/2000000000 : ℝ)^8375 ≤ (31921538960593/100000000000000 : ℝ)^6327 := by
    have hnat : (844080421 : ℕ)^8375*100000000000000^6327 ≤ 31921538960593^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844080421 2000000000 31921538960593 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217933929/500000000 : ℝ), (4501447413/10000000000 : ℝ), (844080421/2000000000 : ℝ)] ![(33313238313699/100000000000000 : ℝ), (6953044542673/20000000000000 : ℝ), (31921538960593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217933929/500000000 : ℝ)|^8375 ≤ (33313238313699/100000000000000 : ℝ)^6327
        have hw : |(217933929/500000000 : ℝ)|=(217933929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501447413/10000000000 : ℝ)|^8375 ≤ (6953044542673/20000000000000 : ℝ)^6327
        have hw : |(4501447413/10000000000 : ℝ)|=(4501447413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844080421/2000000000 : ℝ)|^8375 ≤ (31921538960593/100000000000000 : ℝ)^6327
        have hw : |(844080421/2000000000 : ℝ)|=(844080421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (43/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (43/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (43/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (43/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (43/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (43/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (43/400 : ℝ) ^ (4187/1024 : ℝ) ≤ (10953624564107949/100000000000000000000 : ℝ) := by
    have hpowers : (43/400 : ℝ)^4187 ≤ (10953624564107949/100000000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^4187*100000000000000000000^1024 ≤ 10953624564107949^1024*400^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 400 10953624564107949 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/400 : ℝ)) (X := (10953624564107949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4187/1024 : ℝ) ≤ (20020479545705689/50000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4187 ≤ (20020479545705689/50000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4187*50000000000000000000^1024 ≤ 20020479545705689^1024*2500^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 20020479545705689 50000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (20020479545705689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010953624564107949/50000000000000000000 : ℝ) ≤ (10000535733629617/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50010953624564107949/50000000000000000000 : ℝ)^1024 ≤ (10000535733629617/10000000000000000 : ℝ)^4187 := by
      have hnat : (50010953624564107949 : ℕ)^1024*10000000000000000^4187 ≤ 10000535733629617^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010953624564107949 50000000000000000000 10000535733629617 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000535733629617/10000000000000000 : ℝ)) (X := (50010953624564107949/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050994583655519327/100000000000000000000 : ℝ) ≤ (10001246916613371/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (100050994583655519327/100000000000000000000 : ℝ)^1024 ≤ (10001246916613371/10000000000000000 : ℝ)^4187 := by
      have hnat : (100050994583655519327 : ℕ)^1024*10000000000000000^4187 ≤ 10001246916613371^4187*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050994583655519327 100000000000000000000 10001246916613371 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001246916613371/10000000000000000 : ℝ)) (X := (100050994583655519327/100000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020020479545705689/25000000000000000000 : ℝ) ≤ (80015664796777/80000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (25020020479545705689/25000000000000000000 : ℝ)^1024 ≤ (80015664796777/80000000000000 : ℝ)^4187 := by
      have hnat : (25020020479545705689 : ℕ)^1024*80000000000000^4187 ≤ 80015664796777^4187*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020020479545705689 25000000000000000000 80015664796777 80000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80015664796777/80000000000000 : ℝ)) (X := (25020020479545705689/25000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10953624564107949/100000000000000000000 : ℝ) ≤ ((4008685785770405317/4010000000000000000 : ℝ)+2*(355591491877/200500000000000 : ℝ)*(43/400 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (4008685785770405317/4010000000000000000 : ℝ)+2*(355591491877/200500000000000 : ℝ)*(43/400 : ℝ)=(10000535733629617/10000000000000000 : ℝ) by norm_num, show 1+2*(10953624564107949/100000000000000000000 : ℝ)=(50010953624564107949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20020479545705689/50000000000000000000 : ℝ)+(10953624564107949/100000000000000000000 : ℝ) ≤ ((4008685785770405317/4010000000000000000 : ℝ)+(355591491877/200500000000000 : ℝ)*((369/2500 : ℝ)+(43/400 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (4008685785770405317/4010000000000000000 : ℝ)+(355591491877/200500000000000 : ℝ)*((369/2500 : ℝ)+(43/400 : ℝ))=(10001246916613371/10000000000000000 : ℝ) by norm_num, show 1+(20020479545705689/50000000000000000000 : ℝ)+(10953624564107949/100000000000000000000 : ℝ)=(100050994583655519327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20020479545705689/50000000000000000000 : ℝ) ≤ ((4008685785770405317/4010000000000000000 : ℝ)+2*(355591491877/200500000000000 : ℝ)*(369/2500 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (4008685785770405317/4010000000000000000 : ℝ)+2*(355591491877/200500000000000 : ℝ)*(369/2500 : ℝ)=(80015664796777/80000000000000 : ℝ) by norm_num, show 1+2*(20020479545705689/50000000000000000000 : ℝ)=(25020020479545705689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4008685785770405317/4010000000000000000 : ℝ)*(X 1 0+X 2 0)+(355591491877/200500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (369/2500 : ℝ)) (c := (4008685785770405317/4010000000000000000 : ℝ)) (alpha := (355591491877/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4008685785770405317/4010000000000000000 : ℝ)*(X 0 1+X 2 1)+(355591491877/200500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (369/2500 : ℝ)) (c := (4008685785770405317/4010000000000000000 : ℝ)) (alpha := (355591491877/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4008685785770405317/4010000000000000000 : ℝ)*(X 0 2+X 1 2)+(355591491877/200500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (369/2500 : ℝ)) (c := (4008685785770405317/4010000000000000000 : ℝ)) (alpha := (355591491877/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147214679/10000000000 : ℝ)*X 0 0+(5400041301/10000000000 : ℝ)*X 0 1+(210363199/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534654431/1000000000 : ℝ)*X 1 0+(-2218821231/10000000000 : ℝ)*X 1 1+(1051816079/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336636063/2500000000 : ℝ)*X 2 0+(1314770253/2500000000 : ℝ)*X 2 1+(-2218820491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871733201/2000000000 : ℝ)*X 0 0+(1054900663/2500000000 : ℝ)*X 0 1+(2251121377/5000000000 : ℝ)*X 0 2+(871733201/2000000000 : ℝ)*X 1 0+(1054900663/2500000000 : ℝ)*X 1 1+(2251121377/5000000000 : ℝ)*X 1 2+(871733201/2000000000 : ℝ)*X 2 0+(1054900663/2500000000 : ℝ)*X 2 1+(2251121377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268402679/1250000000 : ℝ)*X 0 0+(2629738441/5000000000 : ℝ)*X 0 1+(2699821379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26553647/50000000 : ℝ)*X 1 0+(-2078258351/10000000000 : ℝ)*X 1 1+(2699821437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310729557/10000000000 : ℝ)*X 2 0+(5399642631/10000000000 : ℝ)*X 2 1+(-2078258471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217933929/500000000 : ℝ)*X 0 0+(4501447413/10000000000 : ℝ)*X 0 1+(844080421/2000000000 : ℝ)*X 0 2+(217933929/500000000 : ℝ)*X 1 0+(4501447413/10000000000 : ℝ)*X 1 1+(844080421/2000000000 : ℝ)*X 1 2+(217933929/500000000 : ℝ)*X 2 0+(4501447413/10000000000 : ℝ)*X 2 1+(844080421/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341434719439861083765815481/50125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334557883/20000000000000 : ℝ)*(base19) + (39596893/3125000000000 : ℝ)*(base23) + (18592457/10000000000000 : ℝ)*(lower2) + (363982553/50000000000000 : ℝ)*(upper5) + (1329048568333969/25000000000000 : ℝ)*(major0) + (1329048568333969/25000000000000 : ℝ)*(major1) + (1329048568333969/25000000000000 : ℝ)*(major2) + (7094187326189069/100000000000000 : ℝ)*(sp0) + (7094263271041601/100000000000000 : ℝ)*(sp1) + (709426651576573/10000000000000 : ℝ)*(sp2) + (1769050138356281/50000000000000 : ℝ)*(sp3) + (40228338619/50000000000000 : ℝ)*(sp4) + (283903529/10000000000000 : ℝ)*(sp5) + (5065009341/25000000000000 : ℝ)*(sp7) + (1769060268374963/50000000000000 : ℝ)*(f.failure) + (7094267782866307/100000000000000 : ℝ)*(f.sum) + (75143603817677/10025000000000000000000000000 : ℝ)*base65 + (1083072169264676827/100250000000000000000000000000000 : ℝ)*base68 + (672654504416176827/100250000000000000000000000000000 : ℝ)*base70 + (174736530885573173/100250000000000000000000000000000 : ℝ)*base71 + (21782464925877/10025000000000000000000000000 : ℝ)*base73 + (2236640577939823173/100250000000000000000000000000000 : ℝ)*base75 + (1250447336473073173/100250000000000000000000000000000 : ℝ)*base77 + (726243031216573173/100250000000000000000000000000000 : ℝ)*base79 + (3767781230401/5012500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (23050861/5000000000000000000000 : ℝ)*base90 + (23050861/5000000000000000000000 : ℝ)*base92 + (23050861/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42546144525737573067455901/25062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77534157/10000000000000 : ℝ)*(base19) + (663478509/50000000000000 : ℝ)*(base23) + (19337887/10000000000000 : ℝ)*(upper2) + (4439979/50000000000000 : ℝ)*(upper3) + (2729133/1250000000000 : ℝ)*(upper5) + (1336568793299951/25000000000000 : ℝ)*(major0) + (1336568793299951/25000000000000 : ℝ)*(major1) + (1336568793299951/25000000000000 : ℝ)*(major2) + (15315751749/50000000000000 : ℝ)*(sp1) + (13578980393/50000000000000 : ℝ)*(sp2) + (89180122759239/1250000000000 : ℝ)*(sp4) + (1783594603473513/25000000000000 : ℝ)*(sp5) + (7134381335821317/100000000000000 : ℝ)*(sp6) + (2846512375259/80000000000 : ℝ)*(sp7) + (2846512375259/80000000000 : ℝ)*(f.failure) + (89180122759239/1250000000000 : ℝ)*(f.sum) + (11895724746723/2506250000000000000000000000 : ℝ)*base66 + (2010248530960720533/100250000000000000000000000000000 : ℝ)*base68 + (1074595643990720533/100250000000000000000000000000000 : ℝ)*base70 + (308025943141779467/100250000000000000000000000000000 : ℝ)*base71 + (3983861779337/626562500000000000000000000 : ℝ)*base74 + (1943082867340220533/100250000000000000000000000000000 : ℝ)*base76 + (116838823470533/100250000000000000000000000000000 : ℝ)*base78 + (3932235177015470533/100250000000000000000000000000000 : ℝ)*base80 + (30850134965817/10025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (36027/8000000000000000000 : ℝ)*base89 + (36027/8000000000000000000 : ℝ)*base91 + (36027/8000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s5_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073884119/5000000000 : ℝ)*x 0 + (5393883857/10000000000 : ℝ)*x 1 + (2632436971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073884119/5000000000 : ℝ)^8375 ≤ (13054402847269/100000000000000 : ℝ)^6327 := by
    have hnat : (1073884119 : ℕ)^8375*100000000000000^6327 ≤ 13054402847269^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073884119 5000000000 13054402847269 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393883857/10000000000 : ℝ)^8375 ≤ (44169272913533/100000000000000 : ℝ)^6327 := by
    have hnat : (5393883857 : ℕ)^8375*100000000000000^6327 ≤ 44169272913533^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393883857 10000000000 44169272913533 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632436971/5000000000 : ℝ)^8375 ≤ (21388162111593/50000000000000 : ℝ)^6327 := by
    have hnat : (2632436971 : ℕ)^8375*50000000000000^6327 ≤ 21388162111593^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632436971 5000000000 21388162111593 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073884119/5000000000 : ℝ), (5393883857/10000000000 : ℝ), (2632436971/5000000000 : ℝ)] ![(13054402847269/100000000000000 : ℝ), (44169272913533/100000000000000 : ℝ), (21388162111593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073884119/5000000000 : ℝ)|^8375 ≤ (13054402847269/100000000000000 : ℝ)^6327
        have hw : |(-1073884119/5000000000 : ℝ)|=(1073884119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393883857/10000000000 : ℝ)|^8375 ≤ (44169272913533/100000000000000 : ℝ)^6327
        have hw : |(5393883857/10000000000 : ℝ)|=(5393883857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632436971/5000000000 : ℝ)|^8375 ≤ (21388162111593/50000000000000 : ℝ)^6327
        have hw : |(2632436971/5000000000 : ℝ)|=(2632436971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344994913/10000000000 : ℝ)*x 0 + (-442643317/2000000000 : ℝ)*x 1 + (5264873943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344994913/10000000000 : ℝ)^8375 ≤ (2727507785799/6250000000000 : ℝ)^6327 := by
    have hnat : (5344994913 : ℕ)^8375*6250000000000^6327 ≤ 2727507785799^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344994913 10000000000 2727507785799 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442643317/2000000000 : ℝ)^8375 ≤ (3395887793911/25000000000000 : ℝ)^6327 := by
    have hnat : (442643317 : ℕ)^8375*25000000000000^6327 ≤ 3395887793911^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442643317 2000000000 3395887793911 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264873943/10000000000 : ℝ)^8375 ≤ (42776324233941/100000000000000 : ℝ)^6327 := by
    have hnat : (5264873943 : ℕ)^8375*100000000000000^6327 ≤ 42776324233941^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264873943 10000000000 42776324233941 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344994913/10000000000 : ℝ), (-442643317/2000000000 : ℝ), (5264873943/10000000000 : ℝ)] ![(2727507785799/6250000000000 : ℝ), (3395887793911/25000000000000 : ℝ), (42776324233941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344994913/10000000000 : ℝ)|^8375 ≤ (2727507785799/6250000000000 : ℝ)^6327
        have hw : |(5344994913/10000000000 : ℝ)|=(5344994913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442643317/2000000000 : ℝ)|^8375 ≤ (3395887793911/25000000000000 : ℝ)^6327
        have hw : |(-442643317/2000000000 : ℝ)|=(442643317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264873943/10000000000 : ℝ)|^8375 ≤ (42776324233941/100000000000000 : ℝ)^6327
        have hw : |(5264873943/10000000000 : ℝ)|=(5264873943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344994911/10000000000 : ℝ)*x 0 + (658109243/1250000000 : ℝ)*x 1 + (-1106608293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344994911/10000000000 : ℝ)^8375 ≤ (43640124551169/100000000000000 : ℝ)^6327 := by
    have hnat : (5344994911 : ℕ)^8375*100000000000000^6327 ≤ 43640124551169^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344994911 10000000000 43640124551169 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658109243/1250000000 : ℝ)^8375 ≤ (5347040530587/12500000000000 : ℝ)^6327 := by
    have hnat : (658109243 : ℕ)^8375*12500000000000^6327 ≤ 5347040530587^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658109243 1250000000 5347040530587 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106608293/5000000000 : ℝ)^8375 ≤ (1697943897971/12500000000000 : ℝ)^6327 := by
    have hnat : (1106608293 : ℕ)^8375*12500000000000^6327 ≤ 1697943897971^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106608293 5000000000 1697943897971 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344994911/10000000000 : ℝ), (658109243/1250000000 : ℝ), (-1106608293/5000000000 : ℝ)] ![(43640124551169/100000000000000 : ℝ), (5347040530587/12500000000000 : ℝ), (1697943897971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344994911/10000000000 : ℝ)|^8375 ≤ (43640124551169/100000000000000 : ℝ)^6327
        have hw : |(5344994911/10000000000 : ℝ)|=(5344994911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658109243/1250000000 : ℝ)|^8375 ≤ (5347040530587/12500000000000 : ℝ)^6327
        have hw : |(658109243/1250000000 : ℝ)|=(658109243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106608293/5000000000 : ℝ)|^8375 ≤ (1697943897971/12500000000000 : ℝ)^6327
        have hw : |(-1106608293/5000000000 : ℝ)|=(1106608293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54487371/125000000 : ℝ)*x 0 + (4231542693/10000000000 : ℝ)*x 1 + (4490219829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54487371/125000000 : ℝ)^8375 ≤ (4164548216093/12500000000000 : ℝ)^6327 := by
    have hnat : (54487371 : ℕ)^8375*12500000000000^6327 ≤ 4164548216093^6327*125000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54487371 125000000 4164548216093 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231542693/10000000000 : ℝ)^8375 ≤ (16016562578741/50000000000000 : ℝ)^6327 := by
    have hnat : (4231542693 : ℕ)^8375*50000000000000^6327 ≤ 16016562578741^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231542693 10000000000 16016562578741 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490219829/10000000000 : ℝ)^8375 ≤ (8662622274461/25000000000000 : ℝ)^6327 := by
    have hnat : (4490219829 : ℕ)^8375*25000000000000^6327 ≤ 8662622274461^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490219829 10000000000 8662622274461 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54487371/125000000 : ℝ), (4231542693/10000000000 : ℝ), (4490219829/10000000000 : ℝ)] ![(4164548216093/12500000000000 : ℝ), (16016562578741/50000000000000 : ℝ), (8662622274461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54487371/125000000 : ℝ)|^8375 ≤ (4164548216093/12500000000000 : ℝ)^6327
        have hw : |(54487371/125000000 : ℝ)|=(54487371/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231542693/10000000000 : ℝ)|^8375 ≤ (16016562578741/50000000000000 : ℝ)^6327
        have hw : |(4231542693/10000000000 : ℝ)|=(4231542693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490219829/10000000000 : ℝ)|^8375 ≤ (8662622274461/25000000000000 : ℝ)^6327
        have hw : |(4490219829/10000000000 : ℝ)|=(4490219829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-536943341/2500000000 : ℝ)*x 0 + (2632603239/5000000000 : ℝ)*x 1 + (1078710021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536943341/2500000000 : ℝ)^8375 ≤ (13054444088853/100000000000000 : ℝ)^6327 := by
    have hnat : (536943341 : ℕ)^8375*100000000000000^6327 ≤ 13054444088853^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536943341 2500000000 13054444088853 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632603239/5000000000 : ℝ)^8375 ≤ (1711196024759/4000000000000 : ℝ)^6327 := by
    have hnat : (2632603239 : ℕ)^8375*4000000000000^6327 ≤ 1711196024759^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632603239 5000000000 1711196024759 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078710021/2000000000 : ℝ)^8375 ≤ (22082827637511/50000000000000 : ℝ)^6327 := by
    have hnat : (1078710021 : ℕ)^8375*50000000000000^6327 ≤ 22082827637511^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078710021 2000000000 22082827637511 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536943341/2500000000 : ℝ), (2632603239/5000000000 : ℝ), (1078710021/2000000000 : ℝ)] ![(13054444088853/100000000000000 : ℝ), (1711196024759/4000000000000 : ℝ), (22082827637511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536943341/2500000000 : ℝ)|^8375 ≤ (13054444088853/100000000000000 : ℝ)^6327
        have hw : |(-536943341/2500000000 : ℝ)|=(536943341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632603239/5000000000 : ℝ)|^8375 ≤ (1711196024759/4000000000000 : ℝ)^6327
        have hw : |(2632603239/5000000000 : ℝ)|=(2632603239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078710021/2000000000 : ℝ)|^8375 ≤ (22082827637511/50000000000000 : ℝ)^6327
        have hw : |(1078710021/2000000000 : ℝ)|=(1078710021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656107487/5000000000 : ℝ)*x 0 + (-521135063/2500000000 : ℝ)*x 1 + (337096879/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656107487/5000000000 : ℝ)^8375 ≤ (10821551790907/25000000000000 : ℝ)^6327 := by
    have hnat : (2656107487 : ℕ)^8375*25000000000000^6327 ≤ 10821551790907^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656107487 5000000000 10821551790907 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521135063/2500000000 : ℝ)^8375 ≤ (12548137992097/100000000000000 : ℝ)^6327 := by
    have hnat : (521135063 : ℕ)^8375*100000000000000^6327 ≤ 12548137992097^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521135063 2500000000 12548137992097 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337096879/625000000 : ℝ)^8375 ≤ (8833130966123/20000000000000 : ℝ)^6327 := by
    have hnat : (337096879 : ℕ)^8375*20000000000000^6327 ≤ 8833130966123^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337096879 625000000 8833130966123 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656107487/5000000000 : ℝ), (-521135063/2500000000 : ℝ), (337096879/625000000 : ℝ)] ![(10821551790907/25000000000000 : ℝ), (12548137992097/100000000000000 : ℝ), (8833130966123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656107487/5000000000 : ℝ)|^8375 ≤ (10821551790907/25000000000000 : ℝ)^6327
        have hw : |(2656107487/5000000000 : ℝ)|=(2656107487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521135063/2500000000 : ℝ)|^8375 ≤ (12548137992097/100000000000000 : ℝ)^6327
        have hw : |(-521135063/2500000000 : ℝ)|=(521135063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337096879/625000000 : ℝ)|^8375 ≤ (8833130966123/20000000000000 : ℝ)^6327
        have hw : |(337096879/625000000 : ℝ)|=(337096879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312214697/10000000000 : ℝ)*x 0 + (2696775171/5000000000 : ℝ)*x 1 + (-2084540249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312214697/10000000000 : ℝ)^8375 ≤ (43286204175903/100000000000000 : ℝ)^6327 := by
    have hnat : (5312214697 : ℕ)^8375*100000000000000^6327 ≤ 43286204175903^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312214697 10000000000 43286204175903 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696775171/5000000000 : ℝ)^8375 ≤ (44165657843911/100000000000000 : ℝ)^6327 := by
    have hnat : (2696775171 : ℕ)^8375*100000000000000^6327 ≤ 44165657843911^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696775171 5000000000 44165657843911 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084540249/10000000000 : ℝ)^8375 ≤ (12548137968193/100000000000000 : ℝ)^6327 := by
    have hnat : (2084540249 : ℕ)^8375*100000000000000^6327 ≤ 12548137968193^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084540249 10000000000 12548137968193 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312214697/10000000000 : ℝ), (2696775171/5000000000 : ℝ), (-2084540249/10000000000 : ℝ)] ![(43286204175903/100000000000000 : ℝ), (44165657843911/100000000000000 : ℝ), (12548137968193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312214697/10000000000 : ℝ)|^8375 ≤ (43286204175903/100000000000000 : ℝ)^6327
        have hw : |(5312214697/10000000000 : ℝ)|=(5312214697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696775171/5000000000 : ℝ)|^8375 ≤ (44165657843911/100000000000000 : ℝ)^6327
        have hw : |(2696775171/5000000000 : ℝ)|=(2696775171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084540249/10000000000 : ℝ)|^8375 ≤ (12548137968193/100000000000000 : ℝ)^6327
        have hw : |(-2084540249/10000000000 : ℝ)|=(2084540249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s5_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544874993/1250000000 : ℝ)*x 0 + (4489553121/10000000000 : ℝ)*x 1 + (4232211933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544874993/1250000000 : ℝ)^8375 ≤ (33316489571411/100000000000000 : ℝ)^6327 := by
    have hnat : (544874993 : ℕ)^8375*100000000000000^6327 ≤ 33316489571411^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544874993 1250000000 33316489571411 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489553121/10000000000 : ℝ)^8375 ≤ (8660919747551/25000000000000 : ℝ)^6327 := by
    have hnat : (4489553121 : ℕ)^8375*25000000000000^6327 ≤ 8660919747551^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489553121 10000000000 8660919747551 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232211933/10000000000 : ℝ)^8375 ≤ (32039831420331/100000000000000 : ℝ)^6327 := by
    have hnat : (4232211933 : ℕ)^8375*100000000000000^6327 ≤ 32039831420331^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232211933 10000000000 32039831420331 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544874993/1250000000 : ℝ), (4489553121/10000000000 : ℝ), (4232211933/10000000000 : ℝ)] ![(33316489571411/100000000000000 : ℝ), (8660919747551/25000000000000 : ℝ), (32039831420331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544874993/1250000000 : ℝ)|^8375 ≤ (33316489571411/100000000000000 : ℝ)^6327
        have hw : |(544874993/1250000000 : ℝ)|=(544874993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489553121/10000000000 : ℝ)|^8375 ≤ (8660919747551/25000000000000 : ℝ)^6327
        have hw : |(4489553121/10000000000 : ℝ)|=(4489553121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232211933/10000000000 : ℝ)|^8375 ≤ (32039831420331/100000000000000 : ℝ)^6327
        have hw : |(4232211933/10000000000 : ℝ)|=(4232211933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (13186539184361997/100000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^4187 ≤ (13186539184361997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11249 : ℕ)^4187*100000000000000000000^1024 ≤ 13186539184361997^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 13186539184361997 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (13186539184361997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4187/1024 : ℝ) ≤ (34519650843471819/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4187 ≤ (34519650843471819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4187*100000000000000000000^1024 ≤ 34519650843471819^1024*50000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34519650843471819 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34519650843471819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013186539184361997/50000000000000000000 : ℝ) ≤ (10000644932945889/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50013186539184361997/50000000000000000000 : ℝ)^1024 ≤ (10000644932945889/10000000000000000 : ℝ)^4187 := by
      have hnat : (50013186539184361997 : ℕ)^1024*10000000000000000^4187 ≤ 10000644932945889^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013186539184361997 50000000000000000000 10000644932945889 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644932945889/10000000000000000 : ℝ)) (X := (50013186539184361997/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505963273753479227/12500000000000000000 : ℝ) ≤ (10001166523485787/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (12505963273753479227/12500000000000000000 : ℝ)^1024 ≤ (10001166523485787/10000000000000000 : ℝ)^4187 := by
      have hnat : (12505963273753479227 : ℕ)^1024*10000000000000000^4187 ≤ 10001166523485787^4187*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505963273753479227 12500000000000000000 10001166523485787 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166523485787/10000000000000000 : ℝ)) (X := (12505963273753479227/12500000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034519650843471819/50000000000000000000 : ℝ) ≤ (2000337622805137/2000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50034519650843471819/50000000000000000000 : ℝ)^1024 ≤ (2000337622805137/2000000000000000 : ℝ)^4187 := by
      have hnat : (50034519650843471819 : ℕ)^1024*2000000000000000^4187 ≤ 2000337622805137^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034519650843471819 50000000000000000000 2000337622805137 2000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000337622805137/2000000000000000 : ℝ)) (X := (50034519650843471819/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13186539184361997/100000000000000000000 : ℝ) ≤ ((29840190380876853461/29850000000000000000 : ℝ)+2*(260795269949/149250000000000 : ℝ)*(11249/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (29840190380876853461/29850000000000000000 : ℝ)+2*(260795269949/149250000000000 : ℝ)*(11249/100000 : ℝ)=(10000644932945889/10000000000000000 : ℝ) by norm_num, show 1+2*(13186539184361997/100000000000000000000 : ℝ)=(50013186539184361997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34519650843471819/100000000000000000000 : ℝ)+(13186539184361997/100000000000000000000 : ℝ) ≤ ((29840190380876853461/29850000000000000000 : ℝ)+(260795269949/149250000000000 : ℝ)*((7117/50000 : ℝ)+(11249/100000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (29840190380876853461/29850000000000000000 : ℝ)+(260795269949/149250000000000 : ℝ)*((7117/50000 : ℝ)+(11249/100000 : ℝ))=(10001166523485787/10000000000000000 : ℝ) by norm_num, show 1+(34519650843471819/100000000000000000000 : ℝ)+(13186539184361997/100000000000000000000 : ℝ)=(12505963273753479227/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34519650843471819/100000000000000000000 : ℝ) ≤ ((29840190380876853461/29850000000000000000 : ℝ)+2*(260795269949/149250000000000 : ℝ)*(7117/50000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (29840190380876853461/29850000000000000000 : ℝ)+2*(260795269949/149250000000000 : ℝ)*(7117/50000 : ℝ)=(2000337622805137/2000000000000000 : ℝ) by norm_num, show 1+2*(34519650843471819/100000000000000000000 : ℝ)=(50034519650843471819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29840190380876853461/29850000000000000000 : ℝ)*(X 1 0+X 2 0)+(260795269949/149250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29840190380876853461/29850000000000000000 : ℝ)) (alpha := (260795269949/149250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29840190380876853461/29850000000000000000 : ℝ)*(X 0 1+X 2 1)+(260795269949/149250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29840190380876853461/29850000000000000000 : ℝ)) (alpha := (260795269949/149250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29840190380876853461/29850000000000000000 : ℝ)*(X 0 2+X 1 2)+(260795269949/149250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29840190380876853461/29850000000000000000 : ℝ)) (alpha := (260795269949/149250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073884119/5000000000 : ℝ)*X 0 0+(5393883857/10000000000 : ℝ)*X 0 1+(2632436971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344994913/10000000000 : ℝ)*X 1 0+(-442643317/2000000000 : ℝ)*X 1 1+(5264873943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344994911/10000000000 : ℝ)*X 2 0+(658109243/1250000000 : ℝ)*X 2 1+(-1106608293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54487371/125000000 : ℝ)*X 0 0+(4231542693/10000000000 : ℝ)*X 0 1+(4490219829/10000000000 : ℝ)*X 0 2+(54487371/125000000 : ℝ)*X 1 0+(4231542693/10000000000 : ℝ)*X 1 1+(4490219829/10000000000 : ℝ)*X 1 2+(54487371/125000000 : ℝ)*X 2 0+(4231542693/10000000000 : ℝ)*X 2 1+(4490219829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536943341/2500000000 : ℝ)*X 0 0+(2632603239/5000000000 : ℝ)*X 0 1+(1078710021/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656107487/5000000000 : ℝ)*X 1 0+(-521135063/2500000000 : ℝ)*X 1 1+(337096879/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312214697/10000000000 : ℝ)*X 2 0+(2696775171/5000000000 : ℝ)*X 2 1+(-2084540249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544874993/1250000000 : ℝ)*X 0 0+(4489553121/10000000000 : ℝ)*X 0 1+(4232211933/10000000000 : ℝ)*X 0 2+(544874993/1250000000 : ℝ)*X 1 0+(4489553121/10000000000 : ℝ)*X 1 1+(4232211933/10000000000 : ℝ)*X 1 2+(544874993/1250000000 : ℝ)*X 2 0+(4489553121/10000000000 : ℝ)*X 2 1+(4232211933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73994571121833171178902357/31093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233587433/50000000000000 : ℝ)*(base19) + (106920557/25000000000000 : ℝ)*(base23) + (19558521/100000000000000 : ℝ)*(lower2) + (3151007/5000000000000 : ℝ)*(upper3) + (16795207/50000000000000 : ℝ)*(upper5) + (726075213142413/12500000000000 : ℝ)*(major0) + (726075213142413/12500000000000 : ℝ)*(major1) + (726075213142413/12500000000000 : ℝ)*(major2) + (7751355394813349/100000000000000 : ℝ)*(sp0) + (7751367281766861/100000000000000 : ℝ)*(sp1) + (3875683660629749/50000000000000 : ℝ)*(sp2) + (3865828846317653/100000000000000 : ℝ)*(sp3) + (12354128377/100000000000000 : ℝ)*(sp4) + (1683923763/25000000000000 : ℝ)*(sp7) + (1932917791006353/50000000000000 : ℝ)*(f.failure) + (3875683874470863/50000000000000 : ℝ)*(f.sum) + (22471514632307/2487500000000000000000000000 : ℝ)*base65 + (1835472241962447131/124375000000000000000000000000000 : ℝ)*base67 + (1538859250009947131/124375000000000000000000000000000 : ℝ)*base69 + (2587340745650572131/124375000000000000000000000000000 : ℝ)*base71 + (622679217629/310937500000000000000000000 : ℝ)*base73 + (628265871502552869/124375000000000000000000000000000 : ℝ)*base76 + (2683925820391197131/124375000000000000000000000000000 : ℝ)*base77 + (1467386069595572131/124375000000000000000000000000000 : ℝ)*base79 + (2889233934289/4975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8554191/5000000000000000000000 : ℝ)*base90 + (8554191/5000000000000000000000 : ℝ)*base92 + (8554191/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2303207898110117552337/621875000000000000000000000 : ℝ) := by norm_num
    linear_combination (255385491/25000000000000 : ℝ)*(base19) + (326646317/50000000000000 : ℝ)*(base23) + (56389119/100000000000000 : ℝ)*(upper3) + (23563549/100000000000000 : ℝ)*(lower4) + (52043099/100000000000000 : ℝ)*(upper5) + (5838733732655791/100000000000000 : ℝ)*(major0) + (5838733732655791/100000000000000 : ℝ)*(major1) + (5838733732655791/100000000000000 : ℝ)*(major2) + (29705092181/100000000000000 : ℝ)*(sp1) + (7170048449/25000000000000 : ℝ)*(sp2) + (7791577800208707/100000000000000 : ℝ)*(sp4) + (7791547073574561/100000000000000 : ℝ)*(sp5) + (7791548466722277/100000000000000 : ℝ)*(sp6) + (1942944770823919/50000000000000 : ℝ)*(sp7) + (1942944770823919/50000000000000 : ℝ)*(f.failure) + (7791577800208707/100000000000000 : ℝ)*(f.sum) + (33865271721809/7462500000000000000000000000 : ℝ)*base65 + (4523096350949385783/995000000000000000000000000000000 : ℝ)*base68 + (2376790552224385783/995000000000000000000000000000000 : ℝ)*base70 + (16012841586025614217/995000000000000000000000000000000 : ℝ)*base71 + (41898197969893/14925000000000000000000000000 : ℝ)*base73 + (3903154582535614217/995000000000000000000000000000000 : ℝ)*base75 + (4948714655815614217/995000000000000000000000000000000 : ℝ)*base77 + (18766338481889385783/995000000000000000000000000000000 : ℝ)*base80 + (53102809131193/14925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5837007/5000000000000000000000 : ℝ)*base89 + (5837007/5000000000000000000000 : ℝ)*base91 + (5837007/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1182_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1182_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1182_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1182_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
