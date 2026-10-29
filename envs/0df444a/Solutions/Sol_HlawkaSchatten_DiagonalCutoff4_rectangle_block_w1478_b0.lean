-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:30.399403+00:00
-- url     : https://prove2.me/submissions/36ee1d97-98a2-479a-83fb-cbe30a9d5b57

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
theorem support_rectangle_w1478_s0_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-861248339/5000000000 : ℝ)*x 0 + (371218211/625000000 : ℝ)*x 1 + (4840507101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861248339/5000000000 : ℝ)^4453 ≤ (1273394273739/12500000000000 : ℝ)^3429 := by
    have hnat : (861248339 : ℕ)^4453*12500000000000^3429 ≤ 1273394273739^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861248339 5000000000 1273394273739 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371218211/625000000 : ℝ)^4453 ≤ (50837495410493/100000000000000 : ℝ)^3429 := by
    have hnat : (371218211 : ℕ)^4453*100000000000000^3429 ≤ 50837495410493^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371218211 625000000 50837495410493 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4840507101/10000000000 : ℝ)^4453 ≤ (38975350386117/100000000000000 : ℝ)^3429 := by
    have hnat : (4840507101 : ℕ)^4453*100000000000000^3429 ≤ 38975350386117^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840507101 10000000000 38975350386117 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-861248339/5000000000 : ℝ), (371218211/625000000 : ℝ), (4840507101/10000000000 : ℝ)] ![(1273394273739/12500000000000 : ℝ), (50837495410493/100000000000000 : ℝ), (38975350386117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-861248339/5000000000 : ℝ)|^4453 ≤ (1273394273739/12500000000000 : ℝ)^3429
        have hw : |(-861248339/5000000000 : ℝ)|=(861248339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371218211/625000000 : ℝ)|^4453 ≤ (50837495410493/100000000000000 : ℝ)^3429
        have hw : |(371218211/625000000 : ℝ)|=(371218211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4840507101/10000000000 : ℝ)|^4453 ≤ (38975350386117/100000000000000 : ℝ)^3429
        have hw : |(4840507101/10000000000 : ℝ)|=(4840507101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (342838437/625000000 : ℝ)*x 0 + (-2341254681/10000000000 : ℝ)*x 1 + (2420253537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342838437/625000000 : ℝ)^4453 ≤ (2865561996543/6250000000000 : ℝ)^3429 := by
    have hnat : (342838437 : ℕ)^4453*6250000000000^3429 ≤ 2865561996543^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342838437 625000000 2865561996543 6250000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341254681/10000000000 : ℝ)^4453 ≤ (7587828971571/50000000000000 : ℝ)^3429 := by
    have hnat : (2341254681 : ℕ)^4453*50000000000000^3429 ≤ 7587828971571^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341254681 10000000000 7587828971571 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420253537/5000000000 : ℝ)^4453 ≤ (2435959381487/6250000000000 : ℝ)^3429 := by
    have hnat : (2420253537 : ℕ)^4453*6250000000000^3429 ≤ 2435959381487^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420253537 5000000000 2435959381487 6250000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342838437/625000000 : ℝ), (-2341254681/10000000000 : ℝ), (2420253537/5000000000 : ℝ)] ![(2865561996543/6250000000000 : ℝ), (7587828971571/50000000000000 : ℝ), (2435959381487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342838437/625000000 : ℝ)|^4453 ≤ (2865561996543/6250000000000 : ℝ)^3429
        have hw : |(342838437/625000000 : ℝ)|=(342838437/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2341254681/10000000000 : ℝ)|^4453 ≤ (7587828971571/50000000000000 : ℝ)^3429
        have hw : |(-2341254681/10000000000 : ℝ)|=(2341254681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2420253537/5000000000 : ℝ)|^4453 ≤ (2435959381487/6250000000000 : ℝ)^3429
        have hw : |(2420253537/5000000000 : ℝ)|=(2420253537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5485415191/10000000000 : ℝ)*x 0 + (605063363/1250000000 : ℝ)*x 1 + (-468250927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5485415191/10000000000 : ℝ)^4453 ≤ (5731124263089/12500000000000 : ℝ)^3429 := by
    have hnat : (5485415191 : ℕ)^4453*12500000000000^3429 ≤ 5731124263089^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485415191 10000000000 5731124263089 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605063363/1250000000 : ℝ)^4453 ≤ (7795069665239/20000000000000 : ℝ)^3429 := by
    have hnat : (605063363 : ℕ)^4453*20000000000000^3429 ≤ 7795069665239^3429*1250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605063363 1250000000 7795069665239 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468250927/2000000000 : ℝ)^4453 ≤ (474239298623/3125000000000 : ℝ)^3429 := by
    have hnat : (468250927 : ℕ)^4453*3125000000000^3429 ≤ 474239298623^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468250927 2000000000 474239298623 3125000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5485415191/10000000000 : ℝ), (605063363/1250000000 : ℝ), (-468250927/2000000000 : ℝ)] ![(5731124263089/12500000000000 : ℝ), (7795069665239/20000000000000 : ℝ), (474239298623/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5485415191/10000000000 : ℝ)|^4453 ≤ (5731124263089/12500000000000 : ℝ)^3429
        have hw : |(5485415191/10000000000 : ℝ)|=(5485415191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605063363/1250000000 : ℝ)|^4453 ≤ (7795069665239/20000000000000 : ℝ)^3429
        have hw : |(605063363/1250000000 : ℝ)|=(605063363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468250927/2000000000 : ℝ)|^4453 ≤ (474239298623/3125000000000 : ℝ)^3429
        have hw : |(-468250927/2000000000 : ℝ)|=(468250927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154442073/10000000000 : ℝ)*x 0 + (3091525099/10000000000 : ℝ)*x 1 + (34524869/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154442073/10000000000 : ℝ)^4453 ≤ (3994840308297/12500000000000 : ℝ)^3429 := by
    have hnat : (4154442073 : ℕ)^4453*12500000000000^3429 ≤ 3994840308297^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154442073 10000000000 3994840308297 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091525099/10000000000 : ℝ)^4453 ≤ (4354651518009/20000000000000 : ℝ)^3429 := by
    have hnat : (3091525099 : ℕ)^4453*20000000000000^3429 ≤ 4354651518009^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091525099 10000000000 4354651518009 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34524869/62500000 : ℝ)^4453 ≤ (46268019932651/100000000000000 : ℝ)^3429 := by
    have hnat : (34524869 : ℕ)^4453*100000000000000^3429 ≤ 46268019932651^3429*62500000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34524869 62500000 46268019932651 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154442073/10000000000 : ℝ), (3091525099/10000000000 : ℝ), (34524869/62500000 : ℝ)] ![(3994840308297/12500000000000 : ℝ), (4354651518009/20000000000000 : ℝ), (46268019932651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154442073/10000000000 : ℝ)|^4453 ≤ (3994840308297/12500000000000 : ℝ)^3429
        have hw : |(4154442073/10000000000 : ℝ)|=(4154442073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091525099/10000000000 : ℝ)|^4453 ≤ (4354651518009/20000000000000 : ℝ)^3429
        have hw : |(3091525099/10000000000 : ℝ)|=(3091525099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34524869/62500000 : ℝ)|^4453 ≤ (46268019932651/100000000000000 : ℝ)^3429
        have hw : |(34524869/62500000 : ℝ)|=(34524869/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431579657/2500000000 : ℝ)*x 0 + (608588801/1250000000 : ℝ)*x 1 + (5910273457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431579657/2500000000 : ℝ)^4453 ≤ (10216517734763/100000000000000 : ℝ)^3429 := by
    have hnat : (431579657 : ℕ)^4453*100000000000000^3429 ≤ 10216517734763^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431579657 2500000000 10216517734763 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608588801/1250000000 : ℝ)^4453 ≤ (7854102629377/20000000000000 : ℝ)^3429 := by
    have hnat : (608588801 : ℕ)^4453*20000000000000^3429 ≤ 7854102629377^3429*1250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608588801 1250000000 7854102629377 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5910273457/10000000000 : ℝ)^4453 ≤ (25256484555129/50000000000000 : ℝ)^3429 := by
    have hnat : (5910273457 : ℕ)^4453*50000000000000^3429 ≤ 25256484555129^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910273457 10000000000 25256484555129 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431579657/2500000000 : ℝ), (608588801/1250000000 : ℝ), (5910273457/10000000000 : ℝ)] ![(10216517734763/100000000000000 : ℝ), (7854102629377/20000000000000 : ℝ), (25256484555129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431579657/2500000000 : ℝ)|^4453 ≤ (10216517734763/100000000000000 : ℝ)^3429
        have hw : |(-431579657/2500000000 : ℝ)|=(431579657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608588801/1250000000 : ℝ)|^4453 ≤ (7854102629377/20000000000000 : ℝ)^3429
        have hw : |(608588801/1250000000 : ℝ)|=(608588801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5910273457/10000000000 : ℝ)|^4453 ≤ (25256484555129/50000000000000 : ℝ)^3429
        have hw : |(5910273457/10000000000 : ℝ)|=(5910273457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185355307/10000000000 : ℝ)*x 0 + (-317872047/2500000000 : ℝ)*x 1 + (118205469/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185355307/10000000000 : ℝ)^4453 ≤ (1065474418787/2500000000000 : ℝ)^3429 := by
    have hnat : (5185355307 : ℕ)^4453*2500000000000^3429 ≤ 1065474418787^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185355307 10000000000 1065474418787 2500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317872047/2500000000 : ℝ)^4453 ≤ (6868054203791/100000000000000 : ℝ)^3429 := by
    have hnat : (317872047 : ℕ)^4453*100000000000000^3429 ≤ 6868054203791^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317872047 2500000000 6868054203791 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118205469/200000000 : ℝ)^4453 ≤ (10102593806513/20000000000000 : ℝ)^3429 := by
    have hnat : (118205469 : ℕ)^4453*20000000000000^3429 ≤ 10102593806513^3429*200000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118205469 200000000 10102593806513 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185355307/10000000000 : ℝ), (-317872047/2500000000 : ℝ), (118205469/200000000 : ℝ)] ![(1065474418787/2500000000000 : ℝ), (6868054203791/100000000000000 : ℝ), (10102593806513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185355307/10000000000 : ℝ)|^4453 ≤ (1065474418787/2500000000000 : ℝ)^3429
        have hw : |(5185355307/10000000000 : ℝ)|=(5185355307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317872047/2500000000 : ℝ)|^4453 ≤ (6868054203791/100000000000000 : ℝ)^3429
        have hw : |(-317872047/2500000000 : ℝ)|=(317872047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118205469/200000000 : ℝ)|^4453 ≤ (10102593806513/20000000000000 : ℝ)^3429
        have hw : |(118205469/200000000 : ℝ)|=(118205469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_6 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592677603/5000000000 : ℝ)*x 0 + (5910273431/10000000000 : ℝ)*x 1 + (-1271488371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592677603/5000000000 : ℝ)^4453 ≤ (852379513469/2000000000000 : ℝ)^3429 := by
    have hnat : (2592677603 : ℕ)^4453*2000000000000^3429 ≤ 852379513469^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592677603 5000000000 852379513469 2000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910273431/10000000000 : ℝ)^4453 ≤ (25256484410843/50000000000000 : ℝ)^3429 := by
    have hnat : (5910273431 : ℕ)^4453*50000000000000^3429 ≤ 25256484410843^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910273431 10000000000 25256484410843 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271488371/10000000000 : ℝ)^4453 ≤ (3434027743737/50000000000000 : ℝ)^3429 := by
    have hnat : (1271488371 : ℕ)^4453*50000000000000^3429 ≤ 3434027743737^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271488371 10000000000 3434027743737 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592677603/5000000000 : ℝ), (5910273431/10000000000 : ℝ), (-1271488371/10000000000 : ℝ)] ![(852379513469/2000000000000 : ℝ), (25256484410843/50000000000000 : ℝ), (3434027743737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592677603/5000000000 : ℝ)|^4453 ≤ (852379513469/2000000000000 : ℝ)^3429
        have hw : |(2592677603/5000000000 : ℝ)|=(2592677603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910273431/10000000000 : ℝ)|^4453 ≤ (25256484410843/50000000000000 : ℝ)^3429
        have hw : |(5910273431/10000000000 : ℝ)|=(5910273431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1271488371/10000000000 : ℝ)|^4453 ≤ (3434027743737/50000000000000 : ℝ)^3429
        have hw : |(-1271488371/10000000000 : ℝ)|=(1271488371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s0_7 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162900971/10000000000 : ℝ)*x 0 + (2730777437/5000000000 : ℝ)*x 1 + (789048793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162900971/10000000000 : ℝ)^4453 ≤ (6408650368063/20000000000000 : ℝ)^3429 := by
    have hnat : (4162900971 : ℕ)^4453*20000000000000^3429 ≤ 6408650368063^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162900971 10000000000 6408650368063 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730777437/5000000000 : ℝ)^4453 ≤ (45590173242657/100000000000000 : ℝ)^3429 := by
    have hnat : (2730777437 : ℕ)^4453*100000000000000^3429 ≤ 45590173242657^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730777437 5000000000 45590173242657 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789048793/2500000000 : ℝ)^4453 ≤ (22366574898843/100000000000000 : ℝ)^3429 := by
    have hnat : (789048793 : ℕ)^4453*100000000000000^3429 ≤ 22366574898843^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789048793 2500000000 22366574898843 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162900971/10000000000 : ℝ), (2730777437/5000000000 : ℝ), (789048793/2500000000 : ℝ)] ![(6408650368063/20000000000000 : ℝ), (45590173242657/100000000000000 : ℝ), (22366574898843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162900971/10000000000 : ℝ)|^4453 ≤ (6408650368063/20000000000000 : ℝ)^3429
        have hw : |(4162900971/10000000000 : ℝ)|=(4162900971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730777437/5000000000 : ℝ)|^4453 ≤ (45590173242657/100000000000000 : ℝ)^3429
        have hw : |(2730777437/5000000000 : ℝ)|=(2730777437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(789048793/2500000000 : ℝ)|^4453 ≤ (22366574898843/100000000000000 : ℝ)^3429
        have hw : |(789048793/2500000000 : ℝ)|=(789048793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6483/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4451/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4451 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4451*1^1024 ≤ 0^1024*1^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4451/1024 : ℝ) ≤ (1863297698183013967/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4451 ≤ (1863297698183013967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4451*100000000000000000000^1024 ≤ 1863297698183013967^1024*5^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1863297698183013967 100000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1863297698183013967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4451 := by
      have hnat : (1 : ℕ)^1024*1^4451 ≤ 1^4451*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101863297698183013967/100000000000000000000 : ℝ) ≤ (5021281497753341/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (101863297698183013967/100000000000000000000 : ℝ)^1024 ≤ (5021281497753341/5000000000000000 : ℝ)^4451 := by
      have hnat : (101863297698183013967 : ℕ)^1024*5000000000000000^4451 ≤ 5021281497753341^4451*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101863297698183013967 100000000000000000000 5021281497753341 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021281497753341/5000000000000000 : ℝ)) (X := (101863297698183013967/100000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51863297698183013967/50000000000000000000 : ℝ) ≤ (2521281497753341/2500000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (51863297698183013967/50000000000000000000 : ℝ)^1024 ≤ (2521281497753341/2500000000000000 : ℝ)^4451 := by
      have hnat : (51863297698183013967 : ℕ)^1024*2500000000000000^4451 ≤ 2521281497753341^4451*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51863297698183013967 50000000000000000000 2521281497753341 2500000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2521281497753341/2500000000000000 : ℝ)) (X := (51863297698183013967/50000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21281497753341/2000000000000000 : ℝ)*(0 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21281497753341/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1863297698183013967/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21281497753341/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21281497753341/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5021281497753341/5000000000000000 : ℝ) by norm_num, show 1+(1863297698183013967/100000000000000000000 : ℝ)+(0 : ℝ)=(101863297698183013967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1863297698183013967/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21281497753341/2000000000000000 : ℝ)*(2/5 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21281497753341/2000000000000000 : ℝ)*(2/5 : ℝ)=(2521281497753341/2500000000000000 : ℝ) by norm_num, show 1+2*(1863297698183013967/100000000000000000000 : ℝ)=(51863297698183013967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21281497753341/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21281497753341/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21281497753341/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21281497753341/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21281497753341/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21281497753341/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-861248339/5000000000 : ℝ)*X 0 0+(371218211/625000000 : ℝ)*X 0 1+(4840507101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((342838437/625000000 : ℝ)*X 1 0+(-2341254681/10000000000 : ℝ)*X 1 1+(2420253537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5485415191/10000000000 : ℝ)*X 2 0+(605063363/1250000000 : ℝ)*X 2 1+(-468250927/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4154442073/10000000000 : ℝ)*X 0 0+(3091525099/10000000000 : ℝ)*X 0 1+(34524869/62500000 : ℝ)*X 0 2+(4154442073/10000000000 : ℝ)*X 1 0+(3091525099/10000000000 : ℝ)*X 1 1+(34524869/62500000 : ℝ)*X 1 2+(4154442073/10000000000 : ℝ)*X 2 0+(3091525099/10000000000 : ℝ)*X 2 1+(34524869/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431579657/2500000000 : ℝ)*X 0 0+(608588801/1250000000 : ℝ)*X 0 1+(5910273457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185355307/10000000000 : ℝ)*X 1 0+(-317872047/2500000000 : ℝ)*X 1 1+(118205469/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592677603/5000000000 : ℝ)*X 2 0+(5910273431/10000000000 : ℝ)*X 2 1+(-1271488371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4162900971/10000000000 : ℝ)*X 0 0+(2730777437/5000000000 : ℝ)*X 0 1+(789048793/2500000000 : ℝ)*X 0 2+(4162900971/10000000000 : ℝ)*X 1 0+(2730777437/5000000000 : ℝ)*X 1 1+(789048793/2500000000 : ℝ)*X 1 2+(4162900971/10000000000 : ℝ)*X 2 0+(2730777437/5000000000 : ℝ)*X 2 1+(789048793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15949785120926397921849/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10517217/12500000000000 : ℝ)*(base1) + (738914703/100000000000000 : ℝ)*(base19) + (771925341/100000000000000 : ℝ)*(base23) + (2948611/4000000000000 : ℝ)*(upper3) + (24044341/25000000000000 : ℝ)*(upper5) + (66052265623379/10000000000000 : ℝ)*(major0) + (66052265623379/10000000000000 : ℝ)*(major1) + (66052265623379/10000000000000 : ℝ)*(major2) + (909933278846697/100000000000000 : ℝ)*(sp0) + (454967463416853/50000000000000 : ℝ)*(sp1) + (909934893823069/100000000000000 : ℝ)*(sp2) + (51388557723881/12500000000000 : ℝ)*(sp3) + (308879931/12500000000000 : ℝ)*(sp4) + (12430731/1250000000000 : ℝ)*(sp7) + (6423586568551/1562500000000 : ℝ)*(f.failure) + (90993566574841/10000000000000 : ℝ)*(f.sum) + (4173978219239/10000000000000000000000000000 : ℝ)*base65 + (124477242399239/20000000000000000000000000000 : ℝ)*base67 + (63648952699239/20000000000000000000000000000 : ℝ)*base69 + (48346006239239/20000000000000000000000000000 : ℝ)*base71 + (31764670099239/10000000000000000000000000000 : ℝ)*base73 + (150020770479239/20000000000000000000000000000 : ℝ)*base75 + (32835589699239/20000000000000000000000000000 : ℝ)*base77 + (57773071999239/20000000000000000000000000000 : ℝ)*base79 + (21396168309239/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (367137/156250000000000000000 : ℝ)*base89 + (367137/156250000000000000000 : ℝ)*base91 + (367137/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (797268010015888101169779/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454468813/25000000000000 : ℝ)*(base19) + (1806642517/100000000000000 : ℝ)*(base23) + (139859601/100000000000000 : ℝ)*(base32) + (132205307/50000000000000 : ℝ)*(upper3) + (88016691/50000000000000 : ℝ)*(upper5) + (696933338621591/100000000000000 : ℝ)*(major0) + (696933338621591/100000000000000 : ℝ)*(major1) + (696933338621591/100000000000000 : ℝ)*(major2) + (4471804299/100000000000000 : ℝ)*(sp1) + (4600852961/100000000000000 : ℝ)*(sp2) + (960094849198971/100000000000000 : ℝ)*(sp4) + (48004427975971/5000000000000 : ℝ)*(sp5) + (240022110425873/25000000000000 : ℝ)*(sp6) + (433771422428601/100000000000000 : ℝ)*(sp7) + (433771562288201/100000000000000 : ℝ)*(f.failure) + (960094849198971/100000000000000 : ℝ)*(f.sum) + (145281723314469/100000000000000000000000000000 : ℝ)*base66 + (824576033414469/200000000000000000000000000000 : ℝ)*base68 + (369533168814469/200000000000000000000000000000 : ℝ)*base70 + (396795431185531/200000000000000000000000000000 : ℝ)*base71 + (535974414514469/100000000000000000000000000000 : ℝ)*base74 + (294632644614469/200000000000000000000000000000 : ℝ)*base76 + (259575960185531/200000000000000000000000000000 : ℝ)*base77 + (658169240985531/200000000000000000000000000000 : ℝ)*base79 + (327557605514469/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (45018313/10000000000000000000000 : ℝ)*base90 + (45018313/10000000000000000000000 : ℝ)*base92 + (45018313/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1478_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6483/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1478_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1478_s1_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-942725679/5000000000 : ℝ)*x 0 + (1398549051/2500000000 : ℝ)*x 1 + (1270303623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (942725679/5000000000 : ℝ)^4453 ≤ (286400058173/2500000000000 : ℝ)^3429 := by
    have hnat : (942725679 : ℕ)^4453*2500000000000^3429 ≤ 286400058173^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942725679 5000000000 286400058173 2500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398549051/2500000000 : ℝ)^4453 ≤ (23516613048449/50000000000000 : ℝ)^3429 := by
    have hnat : (1398549051 : ℕ)^4453*50000000000000^3429 ≤ 23516613048449^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398549051 2500000000 23516613048449 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270303623/2500000000 : ℝ)^4453 ≤ (33208617243/80000000000 : ℝ)^3429 := by
    have hnat : (1270303623 : ℕ)^4453*80000000000^3429 ≤ 33208617243^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270303623 2500000000 33208617243 80000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-942725679/5000000000 : ℝ), (1398549051/2500000000 : ℝ), (1270303623/2500000000 : ℝ)] ![(286400058173/2500000000000 : ℝ), (23516613048449/50000000000000 : ℝ), (33208617243/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-942725679/5000000000 : ℝ)|^4453 ≤ (286400058173/2500000000000 : ℝ)^3429
        have hw : |(-942725679/5000000000 : ℝ)|=(942725679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398549051/2500000000 : ℝ)|^4453 ≤ (23516613048449/50000000000000 : ℝ)^3429
        have hw : |(1398549051/2500000000 : ℝ)|=(1398549051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270303623/2500000000 : ℝ)|^4453 ≤ (33208617243/80000000000 : ℝ)^3429
        have hw : |(1270303623/2500000000 : ℝ)|=(1270303623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392943829/10000000000 : ℝ)*x 0 + (-2156774861/10000000000 : ℝ)*x 1 + (1270303727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392943829/10000000000 : ℝ)^4453 ≤ (22423905075009/50000000000000 : ℝ)^3429 := by
    have hnat : (5392943829 : ℕ)^4453*50000000000000^3429 ≤ 22423905075009^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392943829 10000000000 22423905075009 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156774861/10000000000 : ℝ)^4453 ≤ (2728282772819/20000000000000 : ℝ)^3429 := by
    have hnat : (2156774861 : ℕ)^4453*20000000000000^3429 ≤ 2728282772819^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156774861 10000000000 2728282772819 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270303727/2500000000 : ℝ)^4453 ≤ (8302155193427/20000000000000 : ℝ)^3429 := by
    have hnat : (1270303727 : ℕ)^4453*20000000000000^3429 ≤ 8302155193427^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270303727 2500000000 8302155193427 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392943829/10000000000 : ℝ), (-2156774861/10000000000 : ℝ), (1270303727/2500000000 : ℝ)] ![(22423905075009/50000000000000 : ℝ), (2728282772819/20000000000000 : ℝ), (8302155193427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392943829/10000000000 : ℝ)|^4453 ≤ (22423905075009/50000000000000 : ℝ)^3429
        have hw : |(5392943829/10000000000 : ℝ)|=(5392943829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156774861/10000000000 : ℝ)|^4453 ≤ (2728282772819/20000000000000 : ℝ)^3429
        have hw : |(-2156774861/10000000000 : ℝ)|=(2156774861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270303727/2500000000 : ℝ)|^4453 ≤ (8302155193427/20000000000000 : ℝ)^3429
        have hw : |(1270303727/2500000000 : ℝ)|=(1270303727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696472181/5000000000 : ℝ)*x 0 + (5081214571/10000000000 : ℝ)*x 1 + (-539193649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696472181/5000000000 : ℝ)^4453 ≤ (44847815906111/100000000000000 : ℝ)^3429 := by
    have hnat : (2696472181 : ℕ)^4453*100000000000000^3429 ≤ 44847815906111^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696472181 5000000000 44847815906111 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081214571/10000000000 : ℝ)^4453 ≤ (10377693097967/25000000000000 : ℝ)^3429 := by
    have hnat : (5081214571 : ℕ)^4453*25000000000000^3429 ≤ 10377693097967^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081214571 10000000000 10377693097967 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539193649/2500000000 : ℝ)^4453 ≤ (13641411687459/100000000000000 : ℝ)^3429 := by
    have hnat : (539193649 : ℕ)^4453*100000000000000^3429 ≤ 13641411687459^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539193649 2500000000 13641411687459 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696472181/5000000000 : ℝ), (5081214571/10000000000 : ℝ), (-539193649/2500000000 : ℝ)] ![(44847815906111/100000000000000 : ℝ), (10377693097967/25000000000000 : ℝ), (13641411687459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696472181/5000000000 : ℝ)|^4453 ≤ (44847815906111/100000000000000 : ℝ)^3429
        have hw : |(2696472181/5000000000 : ℝ)|=(2696472181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081214571/10000000000 : ℝ)|^4453 ≤ (10377693097967/25000000000000 : ℝ)^3429
        have hw : |(5081214571/10000000000 : ℝ)|=(5081214571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539193649/2500000000 : ℝ)|^4453 ≤ (13641411687459/100000000000000 : ℝ)^3429
        have hw : |(-539193649/2500000000 : ℝ)|=(539193649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261991111/10000000000 : ℝ)*x 0 + (7454227/20000000 : ℝ)*x 1 + (4862529501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261991111/10000000000 : ℝ)^4453 ≤ (6607451334879/20000000000000 : ℝ)^3429 := by
    have hnat : (4261991111 : ℕ)^4453*20000000000000^3429 ≤ 6607451334879^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261991111 10000000000 6607451334879 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7454227/20000000 : ℝ)^4453 ≤ (5551392096177/20000000000000 : ℝ)^3429 := by
    have hnat : (7454227 : ℕ)^4453*20000000000000^3429 ≤ 5551392096177^3429*20000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7454227 20000000 5551392096177 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862529501/10000000000 : ℝ)^4453 ≤ (39205782835533/100000000000000 : ℝ)^3429 := by
    have hnat : (4862529501 : ℕ)^4453*100000000000000^3429 ≤ 39205782835533^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862529501 10000000000 39205782835533 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261991111/10000000000 : ℝ), (7454227/20000000 : ℝ), (4862529501/10000000000 : ℝ)] ![(6607451334879/20000000000000 : ℝ), (5551392096177/20000000000000 : ℝ), (39205782835533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261991111/10000000000 : ℝ)|^4453 ≤ (6607451334879/20000000000000 : ℝ)^3429
        have hw : |(4261991111/10000000000 : ℝ)|=(4261991111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7454227/20000000 : ℝ)|^4453 ≤ (5551392096177/20000000000000 : ℝ)^3429
        have hw : |(7454227/20000000 : ℝ)|=(7454227/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862529501/10000000000 : ℝ)|^4453 ≤ (39205782835533/100000000000000 : ℝ)^3429
        have hw : |(4862529501/10000000000 : ℝ)|=(4862529501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885825421/10000000000 : ℝ)*x 0 + (1271808507/2500000000 : ℝ)*x 1 + (5588074729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885825421/10000000000 : ℝ)^4453 ≤ (11458953947893/100000000000000 : ℝ)^3429 := by
    have hnat : (1885825421 : ℕ)^4453*100000000000000^3429 ≤ 11458953947893^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885825421 10000000000 11458953947893 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271808507/2500000000 : ℝ)^4453 ≤ (41574644698229/100000000000000 : ℝ)^3429 := by
    have hnat : (1271808507 : ℕ)^4453*100000000000000^3429 ≤ 41574644698229^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271808507 2500000000 41574644698229 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5588074729/10000000000 : ℝ)^4453 ≤ (46966401340811/100000000000000 : ℝ)^3429 := by
    have hnat : (5588074729 : ℕ)^4453*100000000000000^3429 ≤ 46966401340811^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588074729 10000000000 46966401340811 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885825421/10000000000 : ℝ), (1271808507/2500000000 : ℝ), (5588074729/10000000000 : ℝ)] ![(11458953947893/100000000000000 : ℝ), (41574644698229/100000000000000 : ℝ), (46966401340811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885825421/10000000000 : ℝ)|^4453 ≤ (11458953947893/100000000000000 : ℝ)^3429
        have hw : |(-1885825421/10000000000 : ℝ)|=(1885825421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271808507/2500000000 : ℝ)|^4453 ≤ (41574644698229/100000000000000 : ℝ)^3429
        have hw : |(1271808507/2500000000 : ℝ)|=(1271808507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5588074729/10000000000 : ℝ)|^4453 ≤ (46966401340811/100000000000000 : ℝ)^3429
        have hw : |(5588074729/10000000000 : ℝ)|=(5588074729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629204483/5000000000 : ℝ)*x 0 + (-1649914677/10000000000 : ℝ)*x 1 + (5588074763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629204483/5000000000 : ℝ)^4453 ≤ (43400355012769/100000000000000 : ℝ)^3429 := by
    have hnat : (2629204483 : ℕ)^4453*100000000000000^3429 ≤ 43400355012769^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629204483 5000000000 43400355012769 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1649914677/10000000000 : ℝ)^4453 ≤ (4816621631641/50000000000000 : ℝ)^3429 := by
    have hnat : (1649914677 : ℕ)^4453*50000000000000^3429 ≤ 4816621631641^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649914677 10000000000 4816621631641 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5588074763/10000000000 : ℝ)^4453 ≤ (4696640171191/10000000000000 : ℝ)^3429 := by
    have hnat : (5588074763 : ℕ)^4453*10000000000000^3429 ≤ 4696640171191^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588074763 10000000000 4696640171191 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629204483/5000000000 : ℝ), (-1649914677/10000000000 : ℝ), (5588074763/10000000000 : ℝ)] ![(43400355012769/100000000000000 : ℝ), (4816621631641/50000000000000 : ℝ), (4696640171191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629204483/5000000000 : ℝ)|^4453 ≤ (43400355012769/100000000000000 : ℝ)^3429
        have hw : |(2629204483/5000000000 : ℝ)|=(2629204483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1649914677/10000000000 : ℝ)|^4453 ≤ (4816621631641/50000000000000 : ℝ)^3429
        have hw : |(-1649914677/10000000000 : ℝ)|=(1649914677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5588074763/10000000000 : ℝ)|^4453 ≤ (4696640171191/10000000000000 : ℝ)^3429
        have hw : |(5588074763/10000000000 : ℝ)|=(5588074763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_6 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258408997/10000000000 : ℝ)*x 0 + (5588074731/10000000000 : ℝ)*x 1 + (-41247867/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258408997/10000000000 : ℝ)^4453 ≤ (8680071069007/20000000000000 : ℝ)^3429 := by
    have hnat : (5258408997 : ℕ)^4453*20000000000000^3429 ≤ 8680071069007^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258408997 10000000000 8680071069007 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5588074731/10000000000 : ℝ)^4453 ≤ (46966401362641/100000000000000 : ℝ)^3429 := by
    have hnat : (5588074731 : ℕ)^4453*100000000000000^3429 ≤ 46966401362641^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588074731 10000000000 46966401362641 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41247867/250000000 : ℝ)^4453 ≤ (9633243286029/100000000000000 : ℝ)^3429 := by
    have hnat : (41247867 : ℕ)^4453*100000000000000^3429 ≤ 9633243286029^3429*250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41247867 250000000 9633243286029 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258408997/10000000000 : ℝ), (5588074731/10000000000 : ℝ), (-41247867/250000000 : ℝ)] ![(8680071069007/20000000000000 : ℝ), (46966401362641/100000000000000 : ℝ), (9633243286029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258408997/10000000000 : ℝ)|^4453 ≤ (8680071069007/20000000000000 : ℝ)^3429
        have hw : |(5258408997/10000000000 : ℝ)|=(5258408997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5588074731/10000000000 : ℝ)|^4453 ≤ (46966401362641/100000000000000 : ℝ)^3429
        have hw : |(5588074731/10000000000 : ℝ)|=(5588074731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41247867/250000000 : ℝ)|^4453 ≤ (9633243286029/100000000000000 : ℝ)^3429
        have hw : |(-41247867/250000000 : ℝ)|=(41247867/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s1_7 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4262819189/10000000000 : ℝ)*x 0 + (1212301631/2500000000 : ℝ)*x 1 + (1870331223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262819189/10000000000 : ℝ)^4453 ≤ (8261398181973/25000000000000 : ℝ)^3429 := by
    have hnat : (4262819189 : ℕ)^4453*25000000000000^3429 ≤ 8261398181973^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262819189 10000000000 8261398181973 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212301631/2500000000 : ℝ)^4453 ≤ (39066339891361/100000000000000 : ℝ)^3429 := by
    have hnat : (1212301631 : ℕ)^4453*100000000000000^3429 ≤ 39066339891361^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212301631 2500000000 39066339891361 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870331223/5000000000 : ℝ)^4453 ≤ (6972016839991/25000000000000 : ℝ)^3429 := by
    have hnat : (1870331223 : ℕ)^4453*25000000000000^3429 ≤ 6972016839991^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870331223 5000000000 6972016839991 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262819189/10000000000 : ℝ), (1212301631/2500000000 : ℝ), (1870331223/5000000000 : ℝ)] ![(8261398181973/25000000000000 : ℝ), (39066339891361/100000000000000 : ℝ), (6972016839991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262819189/10000000000 : ℝ)|^4453 ≤ (8261398181973/25000000000000 : ℝ)^3429
        have hw : |(4262819189/10000000000 : ℝ)|=(4262819189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212301631/2500000000 : ℝ)|^4453 ≤ (39066339891361/100000000000000 : ℝ)^3429
        have hw : |(1212301631/2500000000 : ℝ)|=(1212301631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870331223/5000000000 : ℝ)|^4453 ≤ (6972016839991/25000000000000 : ℝ)^3429
        have hw : |(1870331223/5000000000 : ℝ)|=(1870331223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6483/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1969/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (117/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6483/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6483/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6483/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6483/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6483/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6483/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2379/100000 : ℝ) ^ (4451/1024 : ℝ) ≤ (2191021853897/25000000000000000000 : ℝ) := by
    have hpowers : (2379/100000 : ℝ)^4451 ≤ (2191021853897/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2379 : ℕ)^4451*25000000000000000000^1024 ≤ 2191021853897^1024*100000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2379 100000 2191021853897 25000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2379/100000 : ℝ)) (X := (2191021853897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6483/25000 : ℝ) ^ (4451/1024 : ℝ) ≤ (17701616236973879/6250000000000000000 : ℝ) := by
    have hpowers : (6483/25000 : ℝ)^4451 ≤ (17701616236973879/6250000000000000000 : ℝ)^1024 := by
      have hnat : (6483 : ℕ)^4451*6250000000000000000^1024 ≤ 17701616236973879^1024*25000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6483 25000 17701616236973879 6250000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6483/25000 : ℝ)) (X := (17701616236973879/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500002191021853897/12500000000000000000 : ℝ) ≤ (10000000403254321/10000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (12500002191021853897/12500000000000000000 : ℝ)^1024 ≤ (10000000403254321/10000000000000000 : ℝ)^4451 := by
      have hnat : (12500002191021853897 : ℕ)^1024*10000000000000000^4451 ≤ 10000000403254321^4451*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500002191021853897 12500000000000000000 10000000403254321 10000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000403254321/10000000000000000 : ℝ)) (X := (12500002191021853897/12500000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25070808655969749413/25000000000000000000 : ℝ) ≤ (2001301804271183/2000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (25070808655969749413/25000000000000000000 : ℝ)^1024 ≤ (2001301804271183/2000000000000000 : ℝ)^4451 := by
      have hnat : (25070808655969749413 : ℕ)^1024*2000000000000000^4451 ≤ 2001301804271183^4451*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25070808655969749413 25000000000000000000 2001301804271183 2000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001301804271183/2000000000000000 : ℝ)) (X := (25070808655969749413/25000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3142701616236973879/3125000000000000000 : ℝ) ≤ (10013017639457509/10000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (3142701616236973879/3125000000000000000 : ℝ)^1024 ≤ (10013017639457509/10000000000000000 : ℝ)^4451 := by
      have hnat : (3142701616236973879 : ℕ)^1024*10000000000000000^4451 ≤ 10013017639457509^4451*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3142701616236973879 3125000000000000000 10013017639457509 10000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013017639457509/10000000000000000 : ℝ)) (X := (3142701616236973879/3125000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2191021853897/25000000000000000000 : ℝ) ≤ ((26166560165880182029/26170000000000000000 : ℝ)+2*(361589894533/130850000000000 : ℝ)*(2379/100000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (26166560165880182029/26170000000000000000 : ℝ)+2*(361589894533/130850000000000 : ℝ)*(2379/100000 : ℝ)=(10000000403254321/10000000000000000 : ℝ) by norm_num, show 1+2*(2191021853897/25000000000000000000 : ℝ)=(12500002191021853897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17701616236973879/6250000000000000000 : ℝ)+(2191021853897/25000000000000000000 : ℝ) ≤ ((26166560165880182029/26170000000000000000 : ℝ)+(361589894533/130850000000000 : ℝ)*((6483/25000 : ℝ)+(2379/100000 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (26166560165880182029/26170000000000000000 : ℝ)+(361589894533/130850000000000 : ℝ)*((6483/25000 : ℝ)+(2379/100000 : ℝ))=(2001301804271183/2000000000000000 : ℝ) by norm_num, show 1+(17701616236973879/6250000000000000000 : ℝ)+(2191021853897/25000000000000000000 : ℝ)=(25070808655969749413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17701616236973879/6250000000000000000 : ℝ) ≤ ((26166560165880182029/26170000000000000000 : ℝ)+2*(361589894533/130850000000000 : ℝ)*(6483/25000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (26166560165880182029/26170000000000000000 : ℝ)+2*(361589894533/130850000000000 : ℝ)*(6483/25000 : ℝ)=(10013017639457509/10000000000000000 : ℝ) by norm_num, show 1+2*(17701616236973879/6250000000000000000 : ℝ)=(3142701616236973879/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26166560165880182029/26170000000000000000 : ℝ)*(X 1 0+X 2 0)+(361589894533/130850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (2379/100000 : ℝ)) (hi := (6483/25000 : ℝ)) (c := (26166560165880182029/26170000000000000000 : ℝ)) (alpha := (361589894533/130850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26166560165880182029/26170000000000000000 : ℝ)*(X 0 1+X 2 1)+(361589894533/130850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (2379/100000 : ℝ)) (hi := (6483/25000 : ℝ)) (c := (26166560165880182029/26170000000000000000 : ℝ)) (alpha := (361589894533/130850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26166560165880182029/26170000000000000000 : ℝ)*(X 0 2+X 1 2)+(361589894533/130850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (2379/100000 : ℝ)) (hi := (6483/25000 : ℝ)) (c := (26166560165880182029/26170000000000000000 : ℝ)) (alpha := (361589894533/130850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-942725679/5000000000 : ℝ)*X 0 0+(1398549051/2500000000 : ℝ)*X 0 1+(1270303623/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5392943829/10000000000 : ℝ)*X 1 0+(-2156774861/10000000000 : ℝ)*X 1 1+(1270303727/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696472181/5000000000 : ℝ)*X 2 0+(5081214571/10000000000 : ℝ)*X 2 1+(-539193649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261991111/10000000000 : ℝ)*X 0 0+(7454227/20000000 : ℝ)*X 0 1+(4862529501/10000000000 : ℝ)*X 0 2+(4261991111/10000000000 : ℝ)*X 1 0+(7454227/20000000 : ℝ)*X 1 1+(4862529501/10000000000 : ℝ)*X 1 2+(4261991111/10000000000 : ℝ)*X 2 0+(7454227/20000000 : ℝ)*X 2 1+(4862529501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1885825421/10000000000 : ℝ)*X 0 0+(1271808507/2500000000 : ℝ)*X 0 1+(5588074729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629204483/5000000000 : ℝ)*X 1 0+(-1649914677/10000000000 : ℝ)*X 1 1+(5588074763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258408997/10000000000 : ℝ)*X 2 0+(5588074731/10000000000 : ℝ)*X 2 1+(-41247867/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4262819189/10000000000 : ℝ)*X 0 0+(1212301631/2500000000 : ℝ)*X 0 1+(1870331223/5000000000 : ℝ)*X 0 2+(4262819189/10000000000 : ℝ)*X 1 0+(1212301631/2500000000 : ℝ)*X 1 1+(1870331223/5000000000 : ℝ)*X 1 2+(4262819189/10000000000 : ℝ)*X 2 0+(1212301631/2500000000 : ℝ)*X 2 1+(1870331223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7423920708111928045709086383/1308500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762597/3125000000000 : ℝ)*(base1) + (215911841/20000000000000 : ℝ)*(base19) + (318056089/25000000000000 : ℝ)*(base23) + (13630419/20000000000000 : ℝ)*(upper3) + (58312823/25000000000000 : ℝ)*(upper5) + (1415074030446809/100000000000000 : ℝ)*(major0) + (1415074030446809/100000000000000 : ℝ)*(major1) + (1415074030446809/100000000000000 : ℝ)*(major2) + (1949394820069379/100000000000000 : ℝ)*(sp0) + (389880840665079/20000000000000 : ℝ)*(sp1) + (487351002665061/25000000000000 : ℝ)*(sp2) + (440369392366431/50000000000000 : ℝ)*(sp3) + (2621804581/25000000000000 : ℝ)*(sp4) + (3779752659/100000000000000 : ℝ)*(sp7) + (880742588888627/100000000000000 : ℝ)*(f.failure) + (9747026414423/500000000000 : ℝ)*(f.sum) + (7097325396899/13085000000000000000000000000 : ℝ)*base65 + (23840779851793595461/2617000000000000000000000000000000 : ℝ)*base67 + (5888867132681595461/2617000000000000000000000000000000 : ℝ)*base69 + (4662144756334404539/2617000000000000000000000000000000 : ℝ)*base72 + (73863445333609/13085000000000000000000000000 : ℝ)*base73 + (8186965694850404539/2617000000000000000000000000000000 : ℝ)*base76 + (6057285442975404539/2617000000000000000000000000000000 : ℝ)*base78 + (5487543813718404539/2617000000000000000000000000000000 : ℝ)*base80 + (6763378527763/6542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (33871949/10000000000000000000000 : ℝ)*base89 + (33871949/10000000000000000000000 : ℝ)*base91 + (33871949/10000000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222648230434649821195990989/52340000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817446901/100000000000000 : ℝ)*(base19) + (219528597/25000000000000 : ℝ)*(base23) + (23485727/20000000000000 : ℝ)*(upper3) + (18273437/100000000000000 : ℝ)*(lower4) + (81389129/100000000000000 : ℝ)*(upper5) + (57974533692747/4000000000000 : ℝ)*(major0) + (57974533692747/4000000000000 : ℝ)*(major1) + (57974533692747/4000000000000 : ℝ)*(major2) + (4932554977/100000000000000 : ℝ)*(sp1) + (5485433561/100000000000000 : ℝ)*(sp2) + (998321136914431/50000000000000 : ℝ)*(sp4) + (249579565478373/12500000000000 : ℝ)*(sp5) + (1996635910280913/100000000000000 : ℝ)*(sp6) + (225521067253097/25000000000000 : ℝ)*(sp7) + (225521067253097/25000000000000 : ℝ)*(f.failure) + (998321136914431/50000000000000 : ℝ)*(f.sum) + (70726280039/13085000000000000000000000 : ℝ)*base66 + (208636558349396337/104680000000000000000000000000000 : ℝ)*base68 + (85140115539963663/104680000000000000000000000000000 : ℝ)*base69 + (1056492570178876337/104680000000000000000000000000000 : ℝ)*base72 + (6162325046211/2617000000000000000000000000 : ℝ)*base73 + (156555584513163663/104680000000000000000000000000000 : ℝ)*base75 + (420392183911756337/104680000000000000000000000000000 : ℝ)*base78 + (296317635748036337/104680000000000000000000000000000 : ℝ)*base80 + (2184683127413/1308500000000000000000000000 : ℝ)*base81 + (15434839/2500000000000000000000 : ℝ)*base89 + (15434839/2500000000000000000000 : ℝ)*base91 + (15434839/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1478_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6483/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1969/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (117/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1478_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1478_s2_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-478540019/2500000000 : ℝ)*x 0 + (2734828919/5000000000 : ℝ)*x 1 + (5187224437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478540019/2500000000 : ℝ)^4453 ≤ (5841520423391/50000000000000 : ℝ)^3429 := by
    have hnat : (478540019 : ℕ)^4453*50000000000000^3429 ≤ 5841520423391^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478540019 2500000000 5841520423391 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734828919/5000000000 : ℝ)^4453 ≤ (45678031022637/100000000000000 : ℝ)^3429 := by
    have hnat : (2734828919 : ℕ)^4453*100000000000000^3429 ≤ 45678031022637^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734828919 5000000000 45678031022637 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187224437/10000000000 : ℝ)^4453 ≤ (42638928115317/100000000000000 : ℝ)^3429 := by
    have hnat : (5187224437 : ℕ)^4453*100000000000000^3429 ≤ 42638928115317^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187224437 10000000000 42638928115317 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478540019/2500000000 : ℝ), (2734828919/5000000000 : ℝ), (5187224437/10000000000 : ℝ)] ![(5841520423391/50000000000000 : ℝ), (45678031022637/100000000000000 : ℝ), (42638928115317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478540019/2500000000 : ℝ)|^4453 ≤ (5841520423391/50000000000000 : ℝ)^3429
        have hw : |(-478540019/2500000000 : ℝ)|=(478540019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734828919/5000000000 : ℝ)|^4453 ≤ (45678031022637/100000000000000 : ℝ)^3429
        have hw : |(2734828919/5000000000 : ℝ)|=(2734828919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187224437/10000000000 : ℝ)|^4453 ≤ (42638928115317/100000000000000 : ℝ)^3429
        have hw : |(5187224437/10000000000 : ℝ)|=(5187224437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361653071/10000000000 : ℝ)*x 0 + (-2059873301/10000000000 : ℝ)*x 1 + (5187224647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361653071/10000000000 : ℝ)^4453 ≤ (22255090586319/50000000000000 : ℝ)^3429 := by
    have hnat : (5361653071 : ℕ)^4453*50000000000000^3429 ≤ 22255090586319^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361653071 10000000000 22255090586319 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059873301/10000000000 : ℝ)^4453 ≤ (12850888451753/100000000000000 : ℝ)^3429 := by
    have hnat : (2059873301 : ℕ)^4453*100000000000000^3429 ≤ 12850888451753^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059873301 10000000000 12850888451753 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187224647/10000000000 : ℝ)^4453 ≤ (2664933147313/6250000000000 : ℝ)^3429 := by
    have hnat : (5187224647 : ℕ)^4453*6250000000000^3429 ≤ 2664933147313^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187224647 10000000000 2664933147313 6250000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361653071/10000000000 : ℝ), (-2059873301/10000000000 : ℝ), (5187224647/10000000000 : ℝ)] ![(22255090586319/50000000000000 : ℝ), (12850888451753/100000000000000 : ℝ), (2664933147313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361653071/10000000000 : ℝ)|^4453 ≤ (22255090586319/50000000000000 : ℝ)^3429
        have hw : |(5361653071/10000000000 : ℝ)|=(5361653071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059873301/10000000000 : ℝ)|^4453 ≤ (12850888451753/100000000000000 : ℝ)^3429
        have hw : |(-2059873301/10000000000 : ℝ)|=(2059873301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187224647/10000000000 : ℝ)|^4453 ≤ (2664933147313/6250000000000 : ℝ)^3429
        have hw : |(5187224647/10000000000 : ℝ)|=(5187224647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361653219/10000000000 : ℝ)*x 0 + (5187224631/10000000000 : ℝ)*x 1 + (-1029936563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361653219/10000000000 : ℝ)^4453 ≤ (22255091384089/50000000000000 : ℝ)^3429 := by
    have hnat : (5361653219 : ℕ)^4453*50000000000000^3429 ≤ 22255091384089^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361653219 10000000000 22255091384089 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187224631/10000000000 : ℝ)^4453 ≤ (42638930186213/100000000000000 : ℝ)^3429 := by
    have hnat : (5187224631 : ℕ)^4453*100000000000000^3429 ≤ 42638930186213^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187224631 10000000000 42638930186213 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029936563/5000000000 : ℝ)^4453 ≤ (257017740679/2000000000000 : ℝ)^3429 := by
    have hnat : (1029936563 : ℕ)^4453*2000000000000^3429 ≤ 257017740679^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029936563 5000000000 257017740679 2000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361653219/10000000000 : ℝ), (5187224631/10000000000 : ℝ), (-1029936563/5000000000 : ℝ)] ![(22255091384089/50000000000000 : ℝ), (42638930186213/100000000000000 : ℝ), (257017740679/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361653219/10000000000 : ℝ)|^4453 ≤ (22255091384089/50000000000000 : ℝ)^3429
        have hw : |(5361653219/10000000000 : ℝ)|=(5361653219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187224631/10000000000 : ℝ)|^4453 ≤ (42638930186213/100000000000000 : ℝ)^3429
        have hw : |(5187224631/10000000000 : ℝ)|=(5187224631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029936563/5000000000 : ℝ)|^4453 ≤ (257017740679/2000000000000 : ℝ)^3429
        have hw : |(-1029936563/5000000000 : ℝ)|=(1029936563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070617623/2500000000 : ℝ)*x 0 + (3979858307/10000000000 : ℝ)*x 1 + (115124669/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070617623/2500000000 : ℝ)^4453 ≤ (3324355923017/10000000000000 : ℝ)^3429 := by
    have hnat : (1070617623 : ℕ)^4453*10000000000000^3429 ≤ 3324355923017^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070617623 2500000000 3324355923017 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979858307/10000000000 : ℝ)^4453 ≤ (15112849033409/50000000000000 : ℝ)^3429 := by
    have hnat : (3979858307 : ℕ)^4453*50000000000000^3429 ≤ 15112849033409^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979858307 10000000000 15112849033409 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115124669/250000000 : ℝ)^4453 ≤ (36530742685477/100000000000000 : ℝ)^3429 := by
    have hnat : (115124669 : ℕ)^4453*100000000000000^3429 ≤ 36530742685477^3429*250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115124669 250000000 36530742685477 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070617623/2500000000 : ℝ), (3979858307/10000000000 : ℝ), (115124669/250000000 : ℝ)] ![(3324355923017/10000000000000 : ℝ), (15112849033409/50000000000000 : ℝ), (36530742685477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070617623/2500000000 : ℝ)|^4453 ≤ (3324355923017/10000000000000 : ℝ)^3429
        have hw : |(1070617623/2500000000 : ℝ)|=(1070617623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979858307/10000000000 : ℝ)|^4453 ≤ (15112849033409/50000000000000 : ℝ)^3429
        have hw : |(3979858307/10000000000 : ℝ)|=(3979858307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115124669/250000000 : ℝ)|^4453 ≤ (36530742685477/100000000000000 : ℝ)^3429
        have hw : |(115124669/250000000 : ℝ)|=(115124669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914222793/10000000000 : ℝ)*x 0 + (2594529213/5000000000 : ℝ)*x 1 + (5467806631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914222793/10000000000 : ℝ)^4453 ≤ (1168353795421/10000000000000 : ℝ)^3429 := by
    have hnat : (1914222793 : ℕ)^4453*10000000000000^3429 ≤ 1168353795421^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914222793 10000000000 1168353795421 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594529213/5000000000 : ℝ)^4453 ≤ (42658506465879/100000000000000 : ℝ)^3429 := by
    have hnat : (2594529213 : ℕ)^4453*100000000000000^3429 ≤ 42658506465879^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594529213 5000000000 42658506465879 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467806631/10000000000 : ℝ)^4453 ≤ (5707244445591/12500000000000 : ℝ)^3429 := by
    have hnat : (5467806631 : ℕ)^4453*12500000000000^3429 ≤ 5707244445591^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467806631 10000000000 5707244445591 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914222793/10000000000 : ℝ), (2594529213/5000000000 : ℝ), (5467806631/10000000000 : ℝ)] ![(1168353795421/10000000000000 : ℝ), (42658506465879/100000000000000 : ℝ), (5707244445591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914222793/10000000000 : ℝ)|^4453 ≤ (1168353795421/10000000000000 : ℝ)^3429
        have hw : |(-1914222793/10000000000 : ℝ)|=(1914222793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594529213/5000000000 : ℝ)|^4453 ≤ (42658506465879/100000000000000 : ℝ)^3429
        have hw : |(2594529213/5000000000 : ℝ)|=(2594529213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467806631/10000000000 : ℝ)|^4453 ≤ (5707244445591/12500000000000 : ℝ)^3429
        have hw : |(5467806631/10000000000 : ℝ)|=(5467806631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287885463/10000000000 : ℝ)*x 0 + (-355858303/2000000000 : ℝ)*x 1 + (683475833/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287885463/10000000000 : ℝ)^4453 ≤ (43716555750703/100000000000000 : ℝ)^3429 := by
    have hnat : (5287885463 : ℕ)^4453*100000000000000^3429 ≤ 43716555750703^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287885463 10000000000 43716555750703 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355858303/2000000000 : ℝ)^4453 ≤ (5312744155051/50000000000000 : ℝ)^3429 := by
    have hnat : (355858303 : ℕ)^4453*50000000000000^3429 ≤ 5312744155051^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355858303 2000000000 5312744155051 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683475833/1250000000 : ℝ)^4453 ≤ (45657955922579/100000000000000 : ℝ)^3429 := by
    have hnat : (683475833 : ℕ)^4453*100000000000000^3429 ≤ 45657955922579^3429*1250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683475833 1250000000 45657955922579 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287885463/10000000000 : ℝ), (-355858303/2000000000 : ℝ), (683475833/1250000000 : ℝ)] ![(43716555750703/100000000000000 : ℝ), (5312744155051/50000000000000 : ℝ), (45657955922579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287885463/10000000000 : ℝ)|^4453 ≤ (43716555750703/100000000000000 : ℝ)^3429
        have hw : |(5287885463/10000000000 : ℝ)|=(5287885463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355858303/2000000000 : ℝ)|^4453 ≤ (5312744155051/50000000000000 : ℝ)^3429
        have hw : |(-355858303/2000000000 : ℝ)|=(355858303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683475833/1250000000 : ℝ)|^4453 ≤ (45657955922579/100000000000000 : ℝ)^3429
        have hw : |(683475833/1250000000 : ℝ)|=(683475833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_6 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321971449/2500000000 : ℝ)*x 0 + (2733903353/5000000000 : ℝ)*x 1 + (-355858199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321971449/2500000000 : ℝ)^4453 ≤ (8743311865169/20000000000000 : ℝ)^3429 := by
    have hnat : (1321971449 : ℕ)^4453*20000000000000^3429 ≤ 8743311865169^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321971449 2500000000 8743311865169 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733903353/5000000000 : ℝ)^4453 ≤ (22828978189013/50000000000000 : ℝ)^3429 := by
    have hnat : (2733903353 : ℕ)^4453*50000000000000^3429 ≤ 22828978189013^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733903353 5000000000 22828978189013 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355858199/2000000000 : ℝ)^4453 ≤ (5312742138727/50000000000000 : ℝ)^3429 := by
    have hnat : (355858199 : ℕ)^4453*50000000000000^3429 ≤ 5312742138727^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355858199 2000000000 5312742138727 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321971449/2500000000 : ℝ), (2733903353/5000000000 : ℝ), (-355858199/2000000000 : ℝ)] ![(8743311865169/20000000000000 : ℝ), (22828978189013/50000000000000 : ℝ), (5312742138727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321971449/2500000000 : ℝ)|^4453 ≤ (8743311865169/20000000000000 : ℝ)^3429
        have hw : |(1321971449/2500000000 : ℝ)|=(1321971449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733903353/5000000000 : ℝ)|^4453 ≤ (22828978189013/50000000000000 : ℝ)^3429
        have hw : |(2733903353/5000000000 : ℝ)|=(2733903353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355858199/2000000000 : ℝ)|^4453 ≤ (5312742138727/50000000000000 : ℝ)^3429
        have hw : |(-355858199/2000000000 : ℝ)|=(355858199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s2_7 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282609031/10000000000 : ℝ)*x 0 + (4600927079/10000000000 : ℝ)*x 1 + (1991977989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282609031/10000000000 : ℝ)^4453 ≤ (33244955831633/100000000000000 : ℝ)^3429 := by
    have hnat : (4282609031 : ℕ)^4453*100000000000000^3429 ≤ 33244955831633^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282609031 10000000000 33244955831633 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4600927079/10000000000 : ℝ)^4453 ≤ (3648892595711/10000000000000 : ℝ)^3429 := by
    have hnat : (4600927079 : ℕ)^4453*10000000000000^3429 ≤ 3648892595711^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4600927079 10000000000 3648892595711 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991977989/5000000000 : ℝ)^4453 ≤ (3783264775353/12500000000000 : ℝ)^3429 := by
    have hnat : (1991977989 : ℕ)^4453*12500000000000^3429 ≤ 3783264775353^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991977989 5000000000 3783264775353 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282609031/10000000000 : ℝ), (4600927079/10000000000 : ℝ), (1991977989/5000000000 : ℝ)] ![(33244955831633/100000000000000 : ℝ), (3648892595711/10000000000000 : ℝ), (3783264775353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282609031/10000000000 : ℝ)|^4453 ≤ (33244955831633/100000000000000 : ℝ)^3429
        have hw : |(4282609031/10000000000 : ℝ)|=(4282609031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4600927079/10000000000 : ℝ)|^4453 ≤ (3648892595711/10000000000000 : ℝ)^3429
        have hw : |(4600927079/10000000000 : ℝ)|=(4600927079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991977989/5000000000 : ℝ)|^4453 ≤ (3783264775353/12500000000000 : ℝ)^3429
        have hw : |(1991977989/5000000000 : ℝ)|=(1991977989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (117/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (807/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (117/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1969/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (117/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1969/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (117/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1969/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (117/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1969/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (117/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1969/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (117/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1969/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1969/25000 : ℝ) ^ (4451/1024 : ℝ) ≤ (24912336615407/1562500000000000000 : ℝ) := by
    have hpowers : (1969/25000 : ℝ)^4451 ≤ (24912336615407/1562500000000000000 : ℝ)^1024 := by
      have hnat : (1969 : ℕ)^4451*1562500000000000000^1024 ≤ 24912336615407^1024*25000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1969 25000 24912336615407 1562500000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1969/25000 : ℝ)) (X := (24912336615407/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (117/625 : ℝ) ^ (4451/1024 : ℝ) ≤ (26835310818147/39062500000000000 : ℝ) := by
    have hpowers : (117/625 : ℝ)^4451 ≤ (26835310818147/39062500000000000 : ℝ)^1024 := by
      have hnat : (117 : ℕ)^4451*39062500000000000^1024 ≤ 26835310818147^1024*625^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117 625 26835310818147 39062500000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (117/625 : ℝ)) (X := (26835310818147/39062500000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781274912336615407/781250000000000000 : ℝ) ≤ (625004585022609/625000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (781274912336615407/781250000000000000 : ℝ)^1024 ≤ (625004585022609/625000000000000 : ℝ)^4451 := by
      have hnat : (781274912336615407 : ℕ)^1024*625000000000000^4451 ≤ 625004585022609^4451*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781274912336615407 781250000000000000 625004585022609 625000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004585022609/625000000000000 : ℝ)) (X := (781274912336615407/781250000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563598324769341287/1562500000000000000 : ℝ) ≤ (1000161672302843/1000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (1563598324769341287/1562500000000000000 : ℝ)^1024 ≤ (1000161672302843/1000000000000000 : ℝ)^4451 := by
      have hnat : (1563598324769341287 : ℕ)^1024*1000000000000000^4451 ≤ 1000161672302843^4451*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563598324769341287 1562500000000000000 1000161672302843 1000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000161672302843/1000000000000000 : ℝ)) (X := (1563598324769341287/1562500000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (19558085310818147/19531250000000000 : ℝ) ≤ (2500790021423779/2500000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (19558085310818147/19531250000000000 : ℝ)^1024 ≤ (2500790021423779/2500000000000000 : ℝ)^4451 := by
      have hnat : (19558085310818147 : ℕ)^1024*2500000000000000^4451 ≤ 2500790021423779^4451*19531250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19558085310818147 19531250000000000 2500790021423779 2500000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500790021423779/2500000000000000 : ℝ)) (X := (19558085310818147/19531250000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24912336615407/1562500000000000000 : ℝ) ≤ ((6776030279439819629/6777500000000000000 : ℝ)+2*(771681333343/542200000000000 : ℝ)*(1969/25000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (6776030279439819629/6777500000000000000 : ℝ)+2*(771681333343/542200000000000 : ℝ)*(1969/25000 : ℝ)=(625004585022609/625000000000000 : ℝ) by norm_num, show 1+2*(24912336615407/1562500000000000000 : ℝ)=(781274912336615407/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26835310818147/39062500000000000 : ℝ)+(24912336615407/1562500000000000000 : ℝ) ≤ ((6776030279439819629/6777500000000000000 : ℝ)+(771681333343/542200000000000 : ℝ)*((117/625 : ℝ)+(1969/25000 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (6776030279439819629/6777500000000000000 : ℝ)+(771681333343/542200000000000 : ℝ)*((117/625 : ℝ)+(1969/25000 : ℝ))=(1000161672302843/1000000000000000 : ℝ) by norm_num, show 1+(26835310818147/39062500000000000 : ℝ)+(24912336615407/1562500000000000000 : ℝ)=(1563598324769341287/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26835310818147/39062500000000000 : ℝ) ≤ ((6776030279439819629/6777500000000000000 : ℝ)+2*(771681333343/542200000000000 : ℝ)*(117/625 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (6776030279439819629/6777500000000000000 : ℝ)+2*(771681333343/542200000000000 : ℝ)*(117/625 : ℝ)=(2500790021423779/2500000000000000 : ℝ) by norm_num, show 1+2*(26835310818147/39062500000000000 : ℝ)=(19558085310818147/19531250000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6776030279439819629/6777500000000000000 : ℝ)*(X 1 0+X 2 0)+(771681333343/542200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1969/25000 : ℝ)) (hi := (117/625 : ℝ)) (c := (6776030279439819629/6777500000000000000 : ℝ)) (alpha := (771681333343/542200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6776030279439819629/6777500000000000000 : ℝ)*(X 0 1+X 2 1)+(771681333343/542200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1969/25000 : ℝ)) (hi := (117/625 : ℝ)) (c := (6776030279439819629/6777500000000000000 : ℝ)) (alpha := (771681333343/542200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6776030279439819629/6777500000000000000 : ℝ)*(X 0 2+X 1 2)+(771681333343/542200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1969/25000 : ℝ)) (hi := (117/625 : ℝ)) (c := (6776030279439819629/6777500000000000000 : ℝ)) (alpha := (771681333343/542200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-478540019/2500000000 : ℝ)*X 0 0+(2734828919/5000000000 : ℝ)*X 0 1+(5187224437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361653071/10000000000 : ℝ)*X 1 0+(-2059873301/10000000000 : ℝ)*X 1 1+(5187224647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361653219/10000000000 : ℝ)*X 2 0+(5187224631/10000000000 : ℝ)*X 2 1+(-1029936563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070617623/2500000000 : ℝ)*X 0 0+(3979858307/10000000000 : ℝ)*X 0 1+(115124669/250000000 : ℝ)*X 0 2+(1070617623/2500000000 : ℝ)*X 1 0+(3979858307/10000000000 : ℝ)*X 1 1+(115124669/250000000 : ℝ)*X 1 2+(1070617623/2500000000 : ℝ)*X 2 0+(3979858307/10000000000 : ℝ)*X 2 1+(115124669/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914222793/10000000000 : ℝ)*X 0 0+(2594529213/5000000000 : ℝ)*X 0 1+(5467806631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287885463/10000000000 : ℝ)*X 1 0+(-355858303/2000000000 : ℝ)*X 1 1+(683475833/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321971449/2500000000 : ℝ)*X 2 0+(2733903353/5000000000 : ℝ)*X 2 1+(-355858199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4282609031/10000000000 : ℝ)*X 0 0+(4600927079/10000000000 : ℝ)*X 0 1+(1991977989/5000000000 : ℝ)*X 0 2+(4282609031/10000000000 : ℝ)*X 1 0+(4600927079/10000000000 : ℝ)*X 1 1+(1991977989/5000000000 : ℝ)*X 1 2+(4282609031/10000000000 : ℝ)*X 2 0+(4600927079/10000000000 : ℝ)*X 2 1+(1991977989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13150589324339986413741/3388750000000000000000000000 : ℝ) := by norm_num
    linear_combination (342301979/100000000000000 : ℝ)*(base19) + (16464243/5000000000000 : ℝ)*(base23) + (59381227/100000000000000 : ℝ)*(lower2) + (4712259/12500000000000 : ℝ)*(upper3) + (101708029/100000000000000 : ℝ)*(upper5) + (1285086508211039/50000000000000 : ℝ)*(major0) + (1285086508211039/50000000000000 : ℝ)*(major1) + (1285086508211039/50000000000000 : ℝ)*(major2) + (221291381852947/6250000000000 : ℝ)*(sp0) + (3540668945214629/100000000000000 : ℝ)*(sp1) + (885167239557937/25000000000000 : ℝ)*(sp2) + (1279739153853/80000000000 : ℝ)*(sp3) + (448616841/6250000000000 : ℝ)*(sp4) + (534731187/20000000000000 : ℝ)*(sp7) + (319935323194437/20000000000000 : ℝ)*(f.failure) + (55322957617447/1562500000000 : ℝ)*(f.sum) + (17230394547751/6777500000000000000000000000 : ℝ)*base65 + (883539320841772031/338875000000000000000000000000000 : ℝ)*base67 + (923657110267352969/338875000000000000000000000000000 : ℝ)*base70 + (1861040050933397031/338875000000000000000000000000000 : ℝ)*base71 + (54158881736647/13555000000000000000000000000 : ℝ)*base73 + (240059755383977969/338875000000000000000000000000000 : ℝ)*base76 + (2164869892289477969/338875000000000000000000000000000 : ℝ)*base78 + (308884802577272031/338875000000000000000000000000000 : ℝ)*base79 + (6752447718633/13555000000000000000000000000 : ℝ)*base82 + (719419/2000000000000000000000 : ℝ)*base89 + (719419/2000000000000000000000 : ℝ)*base91 + (719419/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1487013657967424621993558427/338875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6295967/3125000000000 : ℝ)*(base19) + (549427939/100000000000000 : ℝ)*(base23) + (52936923/100000000000000 : ℝ)*(upper3) + (18244009/100000000000000 : ℝ)*(lower4) + (136181953/100000000000000 : ℝ)*(upper5) + (2604145790738807/100000000000000 : ℝ)*(major0) + (2604145790738807/100000000000000 : ℝ)*(major1) + (2604145790738807/100000000000000 : ℝ)*(major2) + (89478749/5000000000000 : ℝ)*(sp1) + (806456163/10000000000000 : ℝ)*(sp2) + (71749403044019/2000000000000 : ℝ)*(sp4) + (1793734080577513/50000000000000 : ℝ)*(sp5) + (3587461538211381/100000000000000 : ℝ)*(sp6) + (101301330187939/6250000000000 : ℝ)*(sp7) + (101301330187939/6250000000000 : ℝ)*(f.failure) + (71749403044019/2000000000000 : ℝ)*(f.sum) + (23716241339539/27110000000000000000000000000 : ℝ)*base66 + (7215503302185844897/677750000000000000000000000000000 : ℝ)*base68 + (7725294195882344897/677750000000000000000000000000000 : ℝ)*base70 + (5141504780342344897/677750000000000000000000000000000 : ℝ)*base72 + (50695039091941/27110000000000000000000000000 : ℝ)*base73 + (5933272956985844897/677750000000000000000000000000000 : ℝ)*base76 + (2140617975969344897/677750000000000000000000000000000 : ℝ)*base78 + (12358354896229844897/677750000000000000000000000000000 : ℝ)*base80 + (13973980976869/27110000000000000000000000000 : ℝ)*base82 + (3440493/625000000000000000000 : ℝ)*base89 + (3440493/625000000000000000000 : ℝ)*base91 + (3440493/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1478_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (117/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1969/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1478_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1478_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1478_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1478_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1478_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
